import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from scripts.check_efg_governance import (
    FROZEN_MINIMAL_CORE_STRUCTURES,
    controlled_observed_universe_mapping_is_valid,
    documentation_link_errors,
    frozen_structure_digest,
)


class EFGGovernanceTest(unittest.TestCase):
    START = r"^structure Arena where\s*$"
    END = r"^namespace Arena\s*$"

    def test_minimal_core_compatibility_freeze_is_deferred(self):
        self.assertEqual(FROZEN_MINIMAL_CORE_STRUCTURES, {})

    def test_frozen_structure_digest_ignores_comments_and_whitespace(self):
        compact = """\
structure Arena where
  State : Type*
  Action : State → Type*
  next : (s : State) → Action s → State
namespace Arena
"""
        documented = """\
/-- Carrier documentation may evolve. -/
structure Arena where
  /-- State documentation may evolve too. -/
  State   : Type*

  Action : State → Type*
  next :
    (s : State) → Action s → State

namespace Arena
"""

        self.assertEqual(
            frozen_structure_digest(compact, self.START, self.END),
            frozen_structure_digest(documented, self.START, self.END),
        )

    def test_frozen_structure_digest_detects_field_change(self):
        frozen = """\
structure Arena where
  State : Type*
  Action : State → Type*
  next : (s : State) → Action s → State
namespace Arena
"""
        changed = """\
structure Arena where
  State : Type*
  Action : State → Type*
  next : (s : State) → Action s → State
  payoff : State → Nat
namespace Arena
"""

        self.assertNotEqual(
            frozen_structure_digest(frozen, self.START, self.END),
            frozen_structure_digest(changed, self.START, self.END),
        )

    def test_frozen_structure_digest_rejects_missing_boundary(self):
        source = "structure RenamedArena where\n  State : Type*\n"

        self.assertIsNone(
            frozen_structure_digest(source, self.START, self.END)
        )

    def test_controlled_observed_universe_mapping_keeps_action_and_state_separate(
        self,
    ):
        valid = """\
structure ControlledObservedGame (N : Type uN) where
  base : ControlledGame.{uN, uA, uS} N
  InfoState : N → Type uI
  InfoAction : (i : N) → InfoState i → Type uA
namespace ControlledObservedGame
"""
        state_tied = """\
structure ControlledObservedGame (N : Type uN) where
  base : ControlledGame.{uN, uS, uA} N
  InfoState : N → Type uI
  InfoAction : (i : N) → InfoState i → Type uA
namespace ControlledObservedGame
"""

        self.assertTrue(
            controlled_observed_universe_mapping_is_valid(valid)
        )
        self.assertFalse(
            controlled_observed_universe_mapping_is_valid(state_tied)
        )

    def test_documentation_link_check_accepts_existing_relative_target(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.md"
            target = root / "target.md"
            source.write_text("[target](target.md#section)\n", encoding="utf-8")
            target.write_text("# Section\n", encoding="utf-8")

            self.assertEqual(documentation_link_errors([source]), [])

    def test_documentation_link_check_rejects_missing_relative_target(self):
        with TemporaryDirectory() as directory:
            source = Path(directory) / "source.md"
            source.write_text("[missing](missing.md)\n", encoding="utf-8")

            self.assertEqual(
                documentation_link_errors([source]),
                [f"{source}: unresolved local Markdown link missing.md"],
            )


if __name__ == "__main__":
    unittest.main()
