"""Release artifact selectors must not mix platforms or workflow attempts."""
import ast
import fnmatch
from pathlib import Path
import re
import shlex
import unittest

WORKFLOW = Path(__file__).resolve().parents[2] / ".github/workflows/release-validation.yml"


class ReleaseWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.platforms = [name.strip() for name in re.search(r"        os: \[(.+)\]", self.text)[1].split(",")]
        self.shards = ast.literal_eval("[" + re.search(r"        shard: \[(.+)\]", self.text)[1] + "]")

    @staticmethod
    def render(template, attempt, platform, shard=0):
        return template.replace("${{ github.run_attempt }}", str(attempt)).replace("${{ matrix.os }}", platform).replace("${{ matrix.shard }}", str(shard))

    def test_each_platform_downloads_only_its_own_complete_current_attempt_shards(self):
        upload = re.findall(r"^          name: (negative-.+)$", self.text, re.M)
        download = re.findall(r"^          pattern: (negative-.+)$", self.text, re.M)
        self.assertEqual(len(upload), 1)
        self.assertEqual(len(download), 1)
        self.assertEqual(self.shards, list(range(18)))
        self.assertEqual(set(self.platforms), {"ubuntu-24.04", "macos-15", "macos-15-intel"})
        artifacts = [(attempt, platform, shard, self.render(upload[0], attempt, platform, shard))
                     for attempt in (1, 2) for platform in self.platforms for shard in self.shards]
        self.assertEqual(len({item[3] for item in artifacts}), len(artifacts))
        for platform in self.platforms:
            pattern = self.render(download[0], 2, platform)
            selected = {(attempt, name, shard) for attempt, name, shard, artifact in artifacts
                        if fnmatch.fnmatchcase(artifact, pattern)}
            self.assertEqual(selected, {(2, platform, shard) for shard in self.shards})

    def test_each_platform_reuses_only_its_current_attempt_preflight(self):
        preflight = self.text.split("\n  preflight:", 1)[1].split("\n  negative:", 1)[0]
        negative = self.text.split("\n  negative:", 1)[1].split("\n  quality:", 1)[0]
        upload = re.search(r"^          name: (preflight-.+)$", preflight, re.M)[1]
        download = re.search(r"^          name: (preflight-.+)$", negative, re.M)[1]
        self.assertRegex(negative, r"(?m)^    needs: preflight$")
        self.assertEqual(upload, download)
        artifacts = {(attempt, platform): self.render(upload, attempt, platform)
                     for attempt in (1, 2) for platform in self.platforms}
        self.assertEqual(len(set(artifacts.values())), 6)
        for platform in self.platforms:
            selected = [key for key, value in artifacts.items() if value == self.render(download, 2, platform)]
            self.assertEqual(selected, [(2, platform)])
        self.assertIn("--threads 2 --timeout 2400", preflight)
        self.assertIn("path: target/negative-preflight", negative)
        self.assertNotIn("run-id:", negative)
        self.assertNotIn("repository:", negative)
        self.assertNotIn("actions/cache", negative)

    def test_shard_compile_and_verify_deadlines_leave_job_cleanup_headroom(self):
        negative = self.text.split("\n  negative:", 1)[1].split("\n  quality:", 1)[0]
        command = re.search(r"^        run: (exec python3 scripts/negative-shards.py run .+)$", negative, re.M)[1]
        arguments = shlex.split(self.render(command, 1, self.platforms[0], 0))
        options = dict(zip(arguments[4::2], arguments[5::2]))
        max_controls = (114 + len(self.shards) - 1) // len(self.shards)
        process_budget = max_controls * (int(options['--timeout']) + int(options['--compile-timeout']))
        job_budget = int(re.search(r"^    timeout-minutes: (\d+)$", negative, re.M)[1]) * 60
        self.assertEqual(max_controls, 7)
        self.assertEqual(process_budget, 315 * 60)
        self.assertGreaterEqual(job_budget - process_budget, 30 * 60)

    def test_shard_command_covers_the_matrix_and_never_reduces_whole_crate_verification(self):
        command = re.search(r"^        run: (exec python3 scripts/negative-shards.py run .+)$", self.text, re.M)[1]
        arguments = shlex.split(self.render(command, 1, self.platforms[0], 0))
        self.assertEqual(arguments[:4], ["exec", "python3", "scripts/negative-shards.py", "run"])
        options = dict(zip(arguments[4::2], arguments[5::2]))
        self.assertEqual(set(options), {"--shard-index", "--shard-count", "--output", "--jobs", "--threads", "--timeout", "--compile-timeout", "--preflight"})
        self.assertEqual(int(options["--shard-count"]), len(self.shards))
        self.assertEqual((options["--jobs"], options["--threads"], options["--timeout"]), ("1", "2", "2400"))
        self.assertEqual(options["--compile-timeout"], "300")
        self.assertEqual(options["--preflight"], "target/negative-preflight")
        quality = self.text.split("\n  quality:", 1)[1].split("\n  draft-release:", 1)[0]
        draft = self.text.split("\n  draft-release:", 1)[1]
        self.assertRegex(quality, r"(?m)^    needs: negative$")
        self.assertRegex(draft, r"(?m)^    needs: quality$")
        self.assertIn("run: exec python3 scripts/record-verification.py --negative-shards target/full-negative-shards", quality)
        self.assertIn("pattern: full-validation-${{ github.run_attempt }}-*", draft)
        development = WORKFLOW.with_name("verify.yml").read_text()
        self.assertIn("run: exec python3 scripts/record-development.py", development)


if __name__ == "__main__":
    unittest.main()
