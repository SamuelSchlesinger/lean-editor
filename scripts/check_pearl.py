#!/usr/bin/env python3
"""Keep the paper's Lean listings tied to the implementation it discusses."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent


def normalized(text: str) -> str:
    return " ".join(text.split())


def main() -> None:
    sources = [
        normalized(path.read_text())
        for directory in (ROOT / "LeanEditor", ROOT / "Walk")
        for path in directory.glob("*.lean")
    ]
    sources.append(normalized((ROOT / "Main.lean").read_text()))
    paper = (ROOT / "PEARL.tex").read_text()
    blocks = re.findall(
        r"\\begin\{lstlisting\}\[language=Lean\]\n(.*?)\\end\{lstlisting\}",
        paper,
        re.DOTALL,
    )
    if not blocks:
        raise SystemExit("No Lean listings found in PEARL.tex")
    for index, block in enumerate(blocks, 1):
        if not any(normalized(block) in source for source in sources):
            raise SystemExit(
                f"Listing {index} does not match the source: {block.splitlines()[0]}"
            )
    print(f"All {len(blocks)} Lean listings match the source (ignoring whitespace).")


if __name__ == "__main__":
    main()
