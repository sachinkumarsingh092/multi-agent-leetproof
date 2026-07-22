"""
Agent Container - Dependency Injection container for pipeline agents.

Pipeline agent instances must be created BEFORE DBOS.launch() for proper
registration and recovery support.
"""

from typing import Optional

from logging_config import get_logger
from providers import LLMConfig, ReasoningLevel

logger = get_logger(__name__)


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
        """Initialize pipeline agents with the given LLM config.

        Args:
            config: LLM configuration (provider + model)
        """
        logger.info("Initializing pipeline AgentContainer")

        # Import agents here to avoid circular imports at module level
        from agents.velvet_judge import VelvetJudgeAgent
        from agents.velvet_programmer import VelvetProgrammerAgent
        from agents.velvet_invariant_inferrer import VelvetInvariantInferrerAgent
        from agents.velvet_proof_orchestrator import VelvetProofOrchestratorAgent
        from agents.prover_agent import ProverAgent
        from agents.prover_v2_agent import ProverV2Agent
        from agents.proof_reasoning_agent import ProofReasoningAgent
        from agents.retriever_agent import RetrieverAgent

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

        self.prover = ProverAgent(config, retriever=self.retriever, reasoning=self.reasoning)
        logger.info(f"  Created {ProverAgent.name}")

        self.prover_v2 = ProverV2Agent(config, prover=self.prover, retriever=self.retriever, reasoning=self.reasoning, reasoning_level=ReasoningLevel.MEDIUM)
        logger.info(f"  Created {ProverV2Agent.name}")

        self.orchestrator = VelvetProofOrchestratorAgent(config, prover=self.prover_v2)
        logger.info(f"  Created {VelvetProofOrchestratorAgent.name} (using {self.prover_v2.name})")

        # Build name-to-agent mapping for lookup
        self._agents_by_name = {
            self.judge.name: self.judge,
            self.programmer.name: self.programmer,
            self.inferrer.name: self.inferrer,
            self.orchestrator.name: self.orchestrator,
            self.prover.name: self.prover,
            self.prover_v2.name: self.prover_v2,
            self.reasoning.name: self.reasoning,
            self.retriever.name: self.retriever,
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
