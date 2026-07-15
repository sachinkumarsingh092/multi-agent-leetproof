"""
Agent Container - Dependency Injection container for all agents.

All agent instances must be created BEFORE DBOS.launch() for proper
registration and recovery support. This container initializes all agents
at startup and provides access to them throughout the application.
"""

from typing import Optional

from logging_config import get_logger
from providers import LLMConfig, ReasoningLevel

logger = get_logger(__name__)

LEAN_SYNTH_PROVER_V2_MAX_ITERATIONS = 35
LEAN_SYNTH_PROVER_V2_MAX_LEAN_EXPLORE_CALLS = 8
LEAN_SYNTH_PROVER_V2_CONFIG_NAME = "ProverV2AgentLeanSynth"


class AgentContainer:
    """Container holding all agent instances for dependency injection.

    Usage:
        # At startup, before DBOS.launch()
        config = LLMConfig(provider="anthropic", model="claude-sonnet-4-5")
        container = AgentContainer(config)

        # Then launch DBOS
        DBOS.launch()

        # Use agents from container
        result = await container.programmer.run_workflow(state)
    """

    def __init__(self, config: LLMConfig):
        """Initialize all agents with the given LLM config.

        Args:
            config: LLM configuration (provider + model)
        """
        logger.info("Initializing AgentContainer with all agents")

        # Import agents here to avoid circular imports at module level
        from agents.velvet_judge import VelvetJudgeAgent
        from agents.velvet_programmer import VelvetProgrammerAgent
        from agents.velvet_invariant_inferrer import VelvetInvariantInferrerAgent
        from agents.velvet_proof_orchestrator import VelvetProofOrchestratorAgent
        from agents.spec_gen import SpecGenAgent
        from agents.spec_coach import SpecCoachAgent
        from agents.prover_agent import ProverAgent
        from agents.prover_v2_agent import ProverV2Agent
        from agents.proof_reasoning_agent import ProofReasoningAgent
        from agents.retriever_agent import RetrieverAgent
        from agents.lean_synth_and_verify import LeanSynthAndVerifyAgent
        from agents.dafny_synth import DafnySynthAgent

        # Create shared dependencies first
        self.judge = VelvetJudgeAgent(
            config,
            use_tools=False,
            reasoning_level=ReasoningLevel.LOW,
        )
        logger.info(f"  Created {VelvetJudgeAgent.name}")

        self.reasoning = ProofReasoningAgent(config, reasoning_level=ReasoningLevel.MEDIUM)
        logger.info(f"  Created {ProofReasoningAgent.name}")

        self.retriever = RetrieverAgent(config)
        logger.info(f"  Created {RetrieverAgent.name}")

        # Create agents with injected dependencies
        self.programmer = VelvetProgrammerAgent(config, judge=self.judge)
        logger.info(f"  Created {VelvetProgrammerAgent.name}")

        self.inferrer = VelvetInvariantInferrerAgent(config, judge=self.judge, reasoning=self.reasoning, retriever=self.retriever, reasoning_level=ReasoningLevel.LOW)
        logger.info(f"  Created {VelvetInvariantInferrerAgent.name}")

        self.spec_gen = SpecGenAgent(config)
        logger.info(f"  Created {SpecGenAgent.name}")

        self.spec_coach = SpecCoachAgent(config, reasoning_level=ReasoningLevel.LOW)
        logger.info(f"  Created {SpecCoachAgent.name}")

        self.prover = ProverAgent(config, retriever=self.retriever, reasoning=self.reasoning)
        logger.info(f"  Created {ProverAgent.name}")

        self.prover_v2 = ProverV2Agent(config, prover=self.prover, retriever=self.retriever, reasoning=self.reasoning, reasoning_level=ReasoningLevel.MEDIUM)
        logger.info(f"  Created {ProverV2Agent.name}")

        self.orchestrator = VelvetProofOrchestratorAgent(config, prover=self.prover_v2)
        logger.info(f"  Created {VelvetProofOrchestratorAgent.name} (using {self.prover_v2.name})")

        self.lean_synth_prover_v2 = ProverV2Agent(
            config,
            prover=self.prover,
            retriever=self.retriever,
            reasoning=self.reasoning,
            default_max_iterations=LEAN_SYNTH_PROVER_V2_MAX_ITERATIONS,
            max_lean_explore_calls=LEAN_SYNTH_PROVER_V2_MAX_LEAN_EXPLORE_CALLS,
            config_name=LEAN_SYNTH_PROVER_V2_CONFIG_NAME,
            reasoning_level=ReasoningLevel.MEDIUM,
        )
        logger.info(f"  Created tuned {ProverV2Agent.name} for {LeanSynthAndVerifyAgent.name}")

        self.lean_synth = LeanSynthAndVerifyAgent(config, judge=self.judge, prover=self.lean_synth_prover_v2)
        logger.info(f"  Created {LeanSynthAndVerifyAgent.name} (using tuned {self.lean_synth_prover_v2.name})")

        self.dafny_synth = DafnySynthAgent(config, judge=self.judge)
        logger.info(f"  Created {DafnySynthAgent.name}")

        # Build name-to-agent mapping for lookup
        self._agents_by_name = {
            self.judge.name: self.judge,
            self.programmer.name: self.programmer,
            self.inferrer.name: self.inferrer,
            self.orchestrator.name: self.orchestrator,
            self.spec_gen.name: self.spec_gen,
            self.spec_coach.name: self.spec_coach,
            self.prover.name: self.prover,
            self.prover_v2.name: self.prover_v2,
            self.reasoning.name: self.reasoning,
            self.retriever.name: self.retriever,
            self.lean_synth.name: self.lean_synth,
            self.dafny_synth.name: self.dafny_synth,
        }

        logger.info("AgentContainer initialization complete")

    def get_agent_by_name(self, name: str):
        """Get an agent by its name.

        Args:
            name: The agent's name (e.g., "velvet_programmer")

        Returns:
            The agent instance, or None if not found
        """
        return self._agents_by_name.get(name)


# Global container instance (set during app initialization)
_container: Optional[AgentContainer] = None


def init_container(config: LLMConfig) -> AgentContainer:
    """Initialize the global agent container.

    Must be called BEFORE DBOS.launch(). Can only be called once.

    Args:
        config: LLM configuration (provider + model)

    Returns:
        The initialized AgentContainer

    Raises:
        RuntimeError: If container already initialized
    """
    global _container
    if _container is not None:
        logger.warning("AgentContainer already initialized, returning existing instance")
        return _container
    _container = AgentContainer(config)
    return _container


def get_container() -> AgentContainer:
    """Get the global agent container.

    Raises:
        RuntimeError: If container not initialized
    """
    if _container is None:
        raise RuntimeError(
            "AgentContainer not initialized. Call init_container() before DBOS.launch()"
        )
    return _container
