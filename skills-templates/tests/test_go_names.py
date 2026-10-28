"""Run with: uv run --project skills-templates --with pyyaml python -m unittest discover -s skills-templates/tests."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "shared/scripts"))

from _common import class_of, is_go_name, package_of  # noqa: E402
from generate import root_of  # noqa: E402


class GoNamesTest(unittest.TestCase):
    def test_go_names(self):
        cases = {
            "fmt.Sprintf": ("fmt", "fmt", "fmt"),
            "(*bytes.Buffer).Read": ("bytes.Buffer", "bytes", "bytes"),
            "(io.ReadCloser).Read": ("io.ReadCloser", "io", "io"),
            "net/http.Get": ("net/http", "net/http", "net/http"),
            "github.com/acme/lib/text.Transform":
                ("github.com/acme/lib/text", "github.com/acme/lib/text", "github.com/acme"),
            "example.com/app/lib.Generic[string]":
                ("example.com/app/lib", "example.com/app/lib", "example.com/app"),
            "(*example.com/app/lib.Box[string]).Get[string]":
                ("example.com/app/lib.Box", "example.com/app/lib", "example.com/app"),
        }
        for fqn, (cls, pkg, root) in cases.items():
            with self.subTest(fqn=fqn):
                self.assertTrue(is_go_name(fqn))
                self.assertEqual(class_of(fqn), cls)
                self.assertEqual(package_of(fqn), pkg)
                self.assertEqual(root_of(fqn), root)

    def test_jvm_names(self):
        fqn = "com.google.common.base.Strings#padStart(Ljava/lang/String;IC)Ljava/lang/String;"
        self.assertFalse(is_go_name(fqn))
        self.assertEqual(class_of(fqn), "com.google.common.base.Strings")
        self.assertEqual(package_of(fqn), "com.google.common.base")
        self.assertEqual(root_of(fqn), "com.google")


if __name__ == "__main__":
    unittest.main()
