from __future__ import annotations

import sys
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))

from static_lean_guard import (  # noqa: E402
    DECL_PATTERN,
    DISABLED_LINTER_PATTERN,
    NATIVE_DECIDE_PATTERN,
    TOKEN_PATTERNS,
    strip_comments_and_strings,
)


class StaticLeanGuardTests(unittest.TestCase):
    def test_comments_and_strings_do_not_trigger(self):
        clean = strip_comments_and_strings('-- sorry native_decide\n#check "admit"\n/- axiom hidden : False -/')
        self.assertFalse(any(pattern.search(clean) for pattern in TOKEN_PATTERNS.values()))
        self.assertFalse(DECL_PATTERN.search(clean))

    def test_native_decide_is_rejected(self):
        clean = strip_comments_and_strings("theorem x : True := by native_decide")
        self.assertTrue(TOKEN_PATTERNS["native_decide"].search(clean))

    def test_native_backend_decide_form_is_rejected(self):
        clean = strip_comments_and_strings("example : True := by exact decide +native")
        self.assertTrue(NATIVE_DECIDE_PATTERN.search(clean))

    def test_plain_decide_is_not_native_backend(self):
        clean = strip_comments_and_strings("example : True := by decide")
        self.assertFalse(NATIVE_DECIDE_PATTERN.search(clean))

    def test_disabled_linter_is_rejected(self):
        clean = strip_comments_and_strings("set_option linter.style.nativeDecide false in\n#check True")
        self.assertTrue(DISABLED_LINTER_PATTERN.search(clean))


if __name__ == "__main__":
    unittest.main()
