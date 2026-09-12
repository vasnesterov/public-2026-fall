from __future__ import annotations

from pydantic import Field
from pathlib import Path
import re

from checker.plugins import PluginABC, PluginOutput
from checker.exceptions import PluginExecutionFailed
from checker.plugins.scripts import RunScriptPlugin


def path_to_lean_module(path: str) -> str:
    """
    Converts a linux-style path to a Lean module name.

    Example:
        "Shad/Types/Fold/" -> "Shad.Types.Fold"
    """
    module_name = path.replace("/", ".")
    return module_name

class RunPytestPlugin(RunScriptPlugin):
    """Plugin for running pytest."""

    name = "check_heavy_import"

    class Args(PluginABC.Args):
        origin: str
        target: str
        timeout: int | None = None
        isolate: bool = False
        env_whitelist: list[str] = Field(default_factory=lambda: ['PATH'])

        coverage: bool | int | None = None
        allow_failures: bool = False

    def _run(self, args: Args, *, verbose: bool = False) -> PluginOutput:
        target_path = Path(args.target)

        # Scan all .lean files for forbidden `import Mathlib`
        for lean_file in target_path.rglob("*.lean"):
            with open(lean_file, "r", encoding="utf-8") as f:
                for lineno, line in enumerate(f, 1):
                    if line.strip() == "import Mathlib":
                        raise PluginExecutionFailed(
                            f"""{lean_file}:{lineno}: heavy import `import Mathlib` is forbidden.
                            Please use #min_imports command to minimize the imports.""",
                            percentage=0.0
                        )

        # If everything is OK return 100%
        result = PluginOutput(
            output="No heavy imports found!",
            percentage=1.0,
        )
        return result
