"""
Pipeline stages for LLoom Agent.

This package contains the four main stages of the LLoom pipeline:
1. spec_generate - Specification generation from problem description (includes PBT)
2. code_generate - Velvet code generation from specification
3. invariant_generate - Loop invariant generation and improvement
4. verification - Proof generation and verification

Each stage exports a create_*_workflow() function that returns a compiled
StateGraph for that stage.
"""

from stages.spec_generate import create_spec_generate_workflow
from stages.code_generate import create_code_generate_workflow
from stages.invariant_generate import create_invariant_generate_workflow
from stages.verification import create_verification_workflow

__all__ = [
    "create_spec_generate_workflow",
    "create_code_generate_workflow",
    "create_invariant_generate_workflow",
    "create_verification_workflow",
]
