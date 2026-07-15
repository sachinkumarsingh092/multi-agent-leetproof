from utils.lean_explore_service import (
    _LeanExploreDbMetadata,
    _LeanExploreDeclCategory,
    _classify_decl_category,
    _exclude_enriched_result_reason,
)


class TestLeanExploreDeclCategory:
    def test_classifies_theorems_from_decl_type(self):
        category = _classify_decl_category(
            name="Nat.add_comm",
            decl_type="theorem",
            signature="protected theorem add_comm : ∀ (n m : Nat), n + m = m + n",
            is_projection=False,
        )
        assert category is _LeanExploreDeclCategory.THEOREM

    def test_classifies_instances_from_signature(self):
        category = _classify_decl_category(
            name="List.instMembership",
            decl_type="definition",
            signature="instance : Membership α (List α) where\n  mem l a := Mem a l",
            is_projection=False,
        )
        assert category is _LeanExploreDeclCategory.INSTANCE

    def test_classifies_classes_from_signature(self):
        category = _classify_decl_category(
            name="HAdd",
            decl_type="inductive",
            signature="class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where",
            is_projection=False,
        )
        assert category is _LeanExploreDeclCategory.CLASS

    def test_keeps_projections_as_definitions(self):
        category = _classify_decl_category(
            name="HAdd.hAdd",
            decl_type="definition",
            signature="class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where\n  hAdd : α → β → γ",
            is_projection=True,
        )
        assert category is _LeanExploreDeclCategory.DEFINITION


class TestLeanExploreResultFiltering:
    def test_excludes_internal_results(self):
        assert _exclude_enriched_result_reason(
            _LeanExploreDbMetadata(
                decl_type="theorem",
                module_name="Lean.Data.AssocList",
                is_internal=True,
                is_projection=False,
                category=_LeanExploreDeclCategory.THEOREM,
            )
        ) == "internal"

    def test_excludes_classes_instances_and_projections(self):
        assert _exclude_enriched_result_reason(
            _LeanExploreDbMetadata(category=_LeanExploreDeclCategory.CLASS)
        ) == "class"
        assert _exclude_enriched_result_reason(
            _LeanExploreDbMetadata(category=_LeanExploreDeclCategory.INSTANCE)
        ) == "instance"
        assert _exclude_enriched_result_reason(
            _LeanExploreDbMetadata(is_projection=True)
        ) == "projection"

    def test_keeps_theorems(self):
        assert _exclude_enriched_result_reason(
            _LeanExploreDbMetadata(
                decl_type="theorem",
                module_name="Init.Data.Nat.Basic",
                category=_LeanExploreDeclCategory.THEOREM,
            )
        ) is None
