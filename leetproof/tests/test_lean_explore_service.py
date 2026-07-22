import asyncio
import threading
import time
from types import SimpleNamespace

import pytest

import utils.lean_explore_service as lean_explore_service
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


class TestLeanExploreConcurrency:
    @pytest.mark.asyncio
    async def test_concurrent_searches_enter_shared_service_one_at_a_time(
        self, monkeypatch
    ):
        state_lock = threading.Lock()
        active_calls = 0
        max_active_calls = 0

        class FakeService:
            def search(self, **_kwargs):
                nonlocal active_calls, max_active_calls
                with state_lock:
                    active_calls += 1
                    max_active_calls = max(max_active_calls, active_calls)
                time.sleep(0.05)
                with state_lock:
                    active_calls -= 1
                return SimpleNamespace(results=[])

        monkeypatch.setattr(lean_explore_service, "_service", FakeService())
        monkeypatch.setattr(
            lean_explore_service,
            "_search_circuit_open",
            threading.Event(),
        )

        await asyncio.gather(
            lean_explore_service.semantic_search("first query"),
            lean_explore_service.semantic_search("second query"),
        )

        assert max_active_calls == 1

    @pytest.mark.asyncio
    async def test_search_timeout_opens_circuit_for_later_calls(
        self, monkeypatch
    ):
        search_calls = 0

        class SlowService:
            def search(self, **_kwargs):
                nonlocal search_calls
                search_calls += 1
                time.sleep(0.05)
                return SimpleNamespace(results=[])

        circuit = threading.Event()
        monkeypatch.setattr(lean_explore_service, "_service", SlowService())
        monkeypatch.setattr(
            lean_explore_service,
            "_search_circuit_open",
            circuit,
        )
        monkeypatch.setattr(
            lean_explore_service.Timeouts,
            "LEAN_EXPLORE_SEARCH",
            0.01,
        )

        assert await lean_explore_service.semantic_search("slow query") == []
        assert circuit.is_set()
        assert await lean_explore_service.semantic_search("skipped query") == []
        assert search_calls == 1
        await asyncio.sleep(0.05)

    @pytest.mark.asyncio
    async def test_initialization_timeout_opens_circuit(self, monkeypatch):
        async def slow_initialization():
            await asyncio.sleep(1)

        circuit = threading.Event()
        monkeypatch.setattr(
            lean_explore_service,
            "get_lean_service",
            slow_initialization,
        )
        monkeypatch.setattr(
            lean_explore_service,
            "_search_circuit_open",
            circuit,
        )
        monkeypatch.setattr(
            lean_explore_service.Timeouts,
            "LEAN_EXPLORE_INIT",
            0.01,
        )

        assert await lean_explore_service.semantic_search("query") == []
        assert circuit.is_set()
