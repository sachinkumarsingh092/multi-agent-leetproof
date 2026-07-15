"""Quick smoke test for try_all_tactics with suggestion refinement."""

import asyncio
import logging
from pathlib import Path

from tools.pantograph_client import PantographClient
from utils.lean.constants import PANTOGRAPH_CORE_OPTIONS, VELVET_IMPORTS, PANTOGRAPH_OPTIONS

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

PROJECT_PATH = str(Path(__file__).resolve().parents[1] / "llmgen-experiments")

DEFINITIONS = """\
section Specs
-- Precondition: no requirements on input array
def precondition (s : Array Nat) :=
  True

-- Postcondition: characterize the result based on array emptiness
def postcondition (s : Array Nat) (result : Option Nat) :=
  match result with
  | none => s.size = 0
  | some min =>
      s.size > 0 ∧
      (∃ i, i < s.size ∧ s[i]! = min) ∧
      (∀ j, j < s.size → min ≤ s[j]!)
end Specs
"""

GOAL_0 = """\
theorem goal_0
    (s : Array ℕ)
    (require_1 : precondition s)
    (if_pos : s = #[])
    : postcondition s none := by
    sorry
"""

GOAL_1 = """\
theorem goal_1
    (s : Array ℕ)
    (i : ℕ)
    (minIndex : ℕ)
    (invariant_3 : minIndex < s.size)
    (done_1 : i = s.size)
    (i_1 : ℕ)
    (minIndex_1 : ℕ)
    (if_neg : ¬s = #[])
    (invariant_4 : ∀ j < i, s[minIndex]! ≤ s[j]!)
    (i_2 : i = i_1 ∧ minIndex = minIndex_1)
    : postcondition s (some s[minIndex_1]!) := by
    sorry
"""

GOAL_1_TACTICS = [
    """rcases i_2 with ⟨hi, hmin⟩
    subst hmin
    have hle : ∀ j < s.size, s[minIndex]! ≤ s[j]! := by
      intro j hj
      have : j < i := by simpa [done_1] using hj
      exact invariant_4 j this
    have hpos : 0 < s.size := by
      have : s.size ≠ 0 := by
        intro hs0
        have : s = #[] := (Array.size_eq_zero_iff).1 hs0
        exact if_neg this
      exact Nat.pos_of_ne_zero this
    refine And.intro hpos ?_
    aesop?;done"""
]


async def main():
    client = PantographClient(
        imports=VELVET_IMPORTS,
        project_path=PROJECT_PATH,
        options=PANTOGRAPH_OPTIONS,
        core_options=PANTOGRAPH_CORE_OPTIONS,
        timeout=240,
    )
    try:
        await client.load_definitions("specs", DEFINITIONS)

        # --- goal_0: aesop? ---
        logger.info("=== goal_0 with aesop? ===")
        result_0 = await client.try_all_tactics(GOAL_0, ["aesop?"])
        logger.info(f"goal_0 success: {result_0.success}")
        logger.info(f"goal_0 tactic: {result_0.tactic}")
        logger.info(f"goal_0 proof:\n{result_0.proof}")

        # --- goal_1: multi-line tactic with aesop? ---
        logger.info("=== goal_1 with multi-line tactic ===")
        result_1 = await client.try_all_tactics(GOAL_1, GOAL_1_TACTICS)
        logger.info(f"goal_1 success: {result_1.success}")
        logger.info(f"goal_1 tactic: {result_1.tactic}")
        logger.info(f"goal_1 proof:\n{result_1.proof}")
    finally:
        client.close()


if __name__ == "__main__":
    asyncio.run(main())
