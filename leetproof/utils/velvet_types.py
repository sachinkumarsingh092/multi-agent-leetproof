"""Shared type definitions for Velvet language parsing and analysis."""
from dataclasses import dataclass, field
from typing import List, Optional


@dataclass
class NameInfo:
    """Information about a parameter or return value in Velvet."""
    name: str
    ty: str
    is_mut: bool


@dataclass
class VelvetMethod:
    """Parsed Velvet method definition with parameters and contracts."""
    name: str
    params: List[NameInfo]
    returns: NameInfo
    requires: List[str]
    ensures: List[str]
    body: Optional[str] = None

    def has_while_loop(self) -> bool:
        """Check if the method body contains a while loop."""
        if self.body is None:
            return False
        # Look for 'while' keyword (word boundary check)
        import re
        return bool(re.search(r'\bwhile\b', self.body))

    def has_invariant(self) -> bool:
        """Check if the method body contains loop invariants."""
        if self.body is None:
            return False
        import re
        return bool(re.search(r'\binvariant\b', self.body))
