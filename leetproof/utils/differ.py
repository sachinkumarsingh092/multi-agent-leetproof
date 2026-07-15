"""Generic diff utility for comparing two texts."""

import difflib
from dataclasses import dataclass
from typing import List


@dataclass
class DiffHunk:
    """A chunk of differing content."""
    source: str  # Name of the source (left_name or right_name)
    content: str  # The differing line(s)
    line_start: int  # 1-based line number
    line_end: int  # 1-based line number (inclusive)

    def __repr__(self):
        if self.line_start == self.line_end:
            return f"DiffHunk({self.source!r}, line {self.line_start}: {self.content!r})"
        return f"DiffHunk({self.source!r}, lines {self.line_start}-{self.line_end}: {self.content!r})"


@dataclass
class Differ:
    """Compare two texts and produce structured diffs."""
    left_name: str
    left_content: str
    right_name: str
    right_content: str

    def _left_lines(self) -> List[str]:
        return self.left_content.splitlines(keepends=True)

    def _right_lines(self) -> List[str]:
        return self.right_content.splitlines(keepends=True)

    def diff(self) -> List[DiffHunk]:
        """Compute diff and return list of DiffHunks. Empty list = identical."""
        left_lines = self._left_lines()
        right_lines = self._right_lines()

        matcher = difflib.SequenceMatcher(None, left_lines, right_lines)
        hunks = []

        for op, i1, i2, j1, j2 in matcher.get_opcodes():
            if op == 'equal':
                continue
            elif op == 'delete':
                # Lines only in left
                content = ''.join(left_lines[i1:i2])
                hunks.append(DiffHunk(
                    source=self.left_name,
                    content=content.rstrip('\n'),
                    line_start=i1 + 1,
                    line_end=i2
                ))
            elif op == 'insert':
                # Lines only in right
                content = ''.join(right_lines[j1:j2])
                hunks.append(DiffHunk(
                    source=self.right_name,
                    content=content.rstrip('\n'),
                    line_start=j1 + 1,
                    line_end=j2
                ))
            elif op == 'replace':
                # Lines differ - report both sides
                left_content = ''.join(left_lines[i1:i2])
                right_content = ''.join(right_lines[j1:j2])
                hunks.append(DiffHunk(
                    source=self.left_name,
                    content=left_content.rstrip('\n'),
                    line_start=i1 + 1,
                    line_end=i2
                ))
                hunks.append(DiffHunk(
                    source=self.right_name,
                    content=right_content.rstrip('\n'),
                    line_start=j1 + 1,
                    line_end=j2
                ))

        return hunks

    def is_empty(self) -> bool:
        """True if no differences."""
        return len(self.diff()) == 0

    def only_in_left(self) -> List[DiffHunk]:
        """Get hunks only present in left."""
        return [h for h in self.diff() if h.source == self.left_name]

    def only_in_right(self) -> List[DiffHunk]:
        """Get hunks only present in right."""
        return [h for h in self.diff() if h.source == self.right_name]

    def format(self) -> str:
        """Format as unified diff with +/- markers."""
        left_lines = self._left_lines()
        right_lines = self._right_lines()

        diff_lines = difflib.unified_diff(
            left_lines,
            right_lines,
            fromfile=self.left_name,
            tofile=self.right_name,
            lineterm=''
        )
        return '\n'.join(line.rstrip('\n') for line in diff_lines)
