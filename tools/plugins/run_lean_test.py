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

    name = "run_lean_test"

    class Args(PluginABC.Args):
        origin: str
        target: str
        timeout: int | None = None
        isolate: bool = False
        env_whitelist: list[str] = Field(default_factory=lambda: ['PATH'])

        coverage: bool | int | None = None
        allow_failures: bool = False

    def _run(self, args: Args, *, verbose: bool = False) -> PluginOutput:      
        target_module = path_to_lean_module(args.target)
        target_module += ".Check"
        tests_cmd = ['lake build -q', target_module, '&&', 'lake lean', f"{args.target}/Check.lean", "2>&1"]

        # if "Aeneas" in target_module:
        #     tests_cmd = ['cd', args.target, '&&', 'bash', '../run_aeneas.sh', '&&', 'cd', '-', '&&'] + tests_cmd            

        script_cmd = ' '.join(tests_cmd)

        run_script_args = RunScriptPlugin.Args(
            origin=args.origin,
            script=script_cmd,
            timeout=args.timeout,
            isolate=args.isolate,
            env_whitelist=args.env_whitelist,
        )
        result = super()._run(run_script_args, verbose=verbose)

        try:
            score = int(result.output.split("\n")[-2].strip())
            result.percentage = score / 100.0
        except Exception as e:
            raise PluginExecutionFailed(
                f"Lean test failed",
                output=result.output,
                percentage=0.0
            ) from e

        return result
