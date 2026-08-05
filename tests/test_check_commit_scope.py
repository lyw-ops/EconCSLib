import unittest

from scripts.check_commit_scope import partition_grandfathered_commits


class CommitScopeTest(unittest.TestCase):
    def test_partition_grandfathered_commits_preserves_review_order(self):
        enforced, grandfathered = partition_grandfathered_commits(
            ["old-a", "old-b", "new-a", "new-b"],
            {"old-a", "old-b", "unrelated"},
        )

        self.assertEqual(grandfathered, ["old-a", "old-b"])
        self.assertEqual(enforced, ["new-a", "new-b"])

    def test_partition_without_matching_history_enforces_every_commit(self):
        enforced, grandfathered = partition_grandfathered_commits(
            ["new-a", "new-b"],
            {"unrelated"},
        )

        self.assertEqual(grandfathered, [])
        self.assertEqual(enforced, ["new-a", "new-b"])


if __name__ == "__main__":
    unittest.main()
