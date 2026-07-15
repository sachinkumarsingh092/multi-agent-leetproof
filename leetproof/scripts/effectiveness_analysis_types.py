from dataclasses import dataclass
from typing import Dict, List, Union

@dataclass
class SpecGenBuildStats:
    passed: int
    total: int

@dataclass
class SpecGenAttemptCombinationCount:
    build: Union[bool, str]
    coach: str
    pbt: str
    count: int

@dataclass
class SpecGenEffectivenessReport:
    session: str
    builds: SpecGenBuildStats
    coach_verdict_counts: Dict[str, int]
    attempt_combinations: List[SpecGenAttemptCombinationCount]
    final_outcome: str

@dataclass
class ProgrammerAttempt:
    attempt_no: int
    build_passed: bool
    assertion_failure: bool
    pbt_failure: bool
    judge_verdict: Union[str, None]
    program: str
    outcome: Union[str, None]

@dataclass
class ProgrammerBuildStats:
    total_attempts: int
    build_passed: int
    build_failed: int
    assertion_failures: int
    pbt_failures: int

@dataclass
class ProgrammerJudgeStats:
    triggered: int
    passed: int
    failed: int

@dataclass
class ProgrammerEffectivenessReport:
    session: str
    build_stats: ProgrammerBuildStats
    judge_stats: ProgrammerJudgeStats
    final_outcome: str
    attempts: List[ProgrammerAttempt]

@dataclass
class InferrerAttempt:
    attempt_no: int
    validation_passed: bool
    build_passed: bool
    pbt_failure: bool
    correctness_verdict: Union[str, None]
    counterexample_found: bool
    program: str
    outcome: Union[str, None]

@dataclass
class InferrerBuildStats:
    total_attempts: int
    validation_failed: int
    build_passed: int
    build_failed: int
    pbt_failures: int

@dataclass
class InferrerCorrectnessStats:
    triggered: int
    ok: int
    issues: int
    inconclusive: int
    counterexamples_found: int

@dataclass
class InferrerEffectivenessReport:
    session: str
    build_stats: InferrerBuildStats
    correctness_stats: InferrerCorrectnessStats
    final_outcome: str
    attempts: List[InferrerAttempt]

@dataclass
class LeanSynthAttempt:
    attempt_no: int
    validation_passed: bool
    build_passed: bool
    pbt_failure: bool
    judge_verdict: Union[str, None]
    proof_status: Union[str, None]
    has_sorry: bool
    final_build_passed: bool
    program: str
    outcome: Union[str, None]

@dataclass
class LeanSynthBuildStats:
    total_attempts: int
    validation_failures: int
    build_passed: int
    build_failed: int
    pbt_failures: int

@dataclass
class LeanSynthJudgeStats:
    triggered: int
    passed: int
    failed: int

@dataclass
class LeanSynthProofStats:
    triggered: int
    proven: int
    partial: int
    failed: int
    preparation_failed: int
    final_build_failed: int

@dataclass
class LeanSynthEffectivenessReport:
    session: str
    build_stats: LeanSynthBuildStats
    judge_stats: LeanSynthJudgeStats
    proof_stats: LeanSynthProofStats
    final_outcome: str
    attempts: List[LeanSynthAttempt]

