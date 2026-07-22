"""Iteration, retry, and attempt limits for agents and workflows.

Centralizes all magic numbers related to loop iterations, retries, and maximum attempts.
"""


class Limits:
    """Limits for agent iterations, retries, and attempts."""
    
    # Judge/Orchestration limits
    MAX_JUDGE_REJECTIONS_PER_AGENT = 7  # Max rejections before failing workflow
    
    # LLM tool invocation loop limits
    MAX_LLM_TOOL_ITERATIONS = 10        # Max iterations in LLM tool-calling loop
    MAX_TOOL_CALL_RETRIES = 5           # Max retries per tool call on error
    MAX_HALLUCINATION_RETRIES = 5       # Max retries for tool hallucination errors
    
    # Agent-specific attempt limits
    VELVET_PROGRAMMER_MAX_ATTEMPTS = 15  # Max attempts for programmer agent
    VELVET_INVARIANT_MAX_ATTEMPTS = 15  # Max attempts for invariant inferrer
    
    # Proof search limits
    PROVER_MAX_DEPTH = 4                # Max depth for proof decomposition
    PROVER_MAX_ITERATIONS = 5           # Max iterations in proof search
    PROVER_MAX_ATTEMPTS = 5             # Max attempts for prover
    PROOF_GUIDE_MAX_DEPTH = 3           # Max depth for proof guide suggestions
    VELVET_PROGRAMMER_MAX_ITERATIONS = 5  # Max tool iterations for programmer agent
    VELVET_INVARIANT_MAX_ITERATIONS = 5   # Max tool iterations for invariant inferrer
    VELVET_JUDGE_MAX_ITERATIONS = 5       # Max tool iterations for judge agent
    LEAN_SYNTH_MAX_ITERATIONS = 10        # Max tool iterations for lean synth agent
    
    # Graph/workflow execution
    DEFAULT_RECURSION_LIMIT = 20        # Default recursion limit for graph.invoke
    PIPELINE_RECURSION_LIMIT = 50       # Recursion limit for pipeline execution
    
    # Judge invocation
    JUDGE_MAX_ITERATIONS = 5            # Max tool iterations for judge agent

    # Message and output limits
    MAX_DIAGNOSTIC_MESSAGE_LENGTH = 1000  # Max characters for diagnostic messages
