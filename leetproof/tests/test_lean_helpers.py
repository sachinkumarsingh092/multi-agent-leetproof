from utils.lean.types import Param
from utils.lean_helpers import (
    tuple_projection_expr,
    build_postcondition_application,
    build_lean_impl_pbt_section,
)


def test_tuple_projection_expr_for_multiple_results():
    assert tuple_projection_expr("result", 1, 0) == "result"
    assert tuple_projection_expr("result", 2, 0) == "result.1"
    assert tuple_projection_expr("result", 2, 1) == "result.2"
    assert tuple_projection_expr("result", 3, 0) == "result.1"
    assert tuple_projection_expr("result", 3, 1) == "result.2.1"
    assert tuple_projection_expr("result", 3, 2) == "result.2.2"
    assert tuple_projection_expr("result", 4, 2) == "result.2.2.1"
    assert tuple_projection_expr("result", 4, 3) == "result.2.2.2"


def test_build_postcondition_application_expands_tuple_results():
    precond_params = [Param(name="nums", ty="Array Int")]
    result_params = [
        Param(name="k", ty="Nat"),
        Param(name="out", ty="Array Int"),
    ]

    assert (
        build_postcondition_application(precond_params, result_params)
        == "postcondition nums result.1 result.2"
    )


def test_build_lean_impl_pbt_section_single_result():
    precond_params = [Param(name="xs", ty="Array Int"), Param(name="k", ty="Nat")]
    result_params = [Param(name="result", ty="Array Int")]

    content = build_lean_impl_pbt_section(
        precond_params,
        result_params,
        has_precondition=True,
        max_ms=5000,
    )

    assert "method implementationPbt (xs : Array Int) (k : Nat)" in content
    assert "return (result : Array Int)" in content
    assert "require precondition xs k" in content
    assert "ensures postcondition xs k result" in content
    assert "return (implementation xs k)" in content
    assert "velvet_plausible_test implementationPbt (config := { maxMs := some 5000 })" in content


def test_build_lean_impl_pbt_section_multi_result_uses_projections():
    precond_params = [Param(name="nums", ty="Array Int")]
    result_params = [
        Param(name="k", ty="Nat"),
        Param(name="out", ty="Array Int"),
    ]

    content = build_lean_impl_pbt_section(
        precond_params,
        result_params,
        has_precondition=True,
        max_ms=20000,
    )

    assert "method implementationPbt (nums : Array Int)" in content
    assert "return (result : Nat × Array Int)" in content
    assert "require precondition nums" in content
    assert "ensures postcondition nums result.1 result.2" in content
    assert "return (implementation nums)" in content
    assert "velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })" in content


def test_build_lean_impl_pbt_section_three_results_uses_nested_projections():
    result_params = [
        Param(name="a", ty="Nat"),
        Param(name="b", ty="Array Int"),
        Param(name="c", ty="Bool"),
    ]

    content = build_lean_impl_pbt_section(
        [],
        result_params,
        has_precondition=False,
    )

    assert "return (result : Nat × Array Int × Bool)" in content
    assert "ensures postcondition result.1 result.2.1 result.2.2" in content
    assert "require precondition" not in content
    assert "return implementation" in content
