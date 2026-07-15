"""Tests for tools.proof_search module."""

import random
from unittest.mock import AsyncMock, MagicMock, patch

import pytest
from pantograph.search import SearchState
from pantograph.server import TacticFailure
from utils.lean_explore_service import LeanExploreResult
from utils.lean.types import Goal

from tools.proof_search import (
    TACTIC_WEIGHT_CORE,
    LemmaDiscoveryConfig,
    TopNSelector,
    ProofSearchMCTS,
    ProofSearchResult,
    ProofSearcher,
    ValidatedTacticProofStatus,
    WeightedTactic,
    build_dependency_graph,
    build_tactic_pool,
    discover_lemmas,
    filter_lemmas,
    _is_typeclass_projection,
    not_lean_internal,
    rank_symbols,
)

def _wt(tactics: list[str]) -> list[WeightedTactic]:
    """Helper: wrap plain tactic strings as WeightedTactics for tests."""
    return [WeightedTactic(t, TACTIC_WEIGHT_CORE) for t in tactics]


# ---------------------------------------------------------------------------
# Symbol discovery / ranking tests
# ---------------------------------------------------------------------------

class TestSymbolDiscovery:
    @pytest.mark.asyncio
    async def test_build_dependency_graph_basic(self):
        """BFS should traverse dependencies up to max_depth."""
        client = AsyncMock()
        client.get_dependencies = AsyncMock(side_effect=lambda name: {
            "A": ["B", "C"],
            "B": ["D"],
            "C": [],
            "D": [],
        }.get(name, []))

        graph = await build_dependency_graph(client, ["A"], max_depth=3)

        assert "A" in graph
        assert "B" in graph
        assert "C" in graph
        assert "D" in graph
        assert graph["A"] == ["B", "C"]
        assert graph["B"] == ["D"]

    @pytest.mark.asyncio
    async def test_build_dependency_graph_depth_limit(self):
        """Should stop at max_depth."""
        client = AsyncMock()
        client.get_dependencies = AsyncMock(side_effect=lambda name: {
            "A": ["B"],
            "B": ["C"],
            "C": ["D"],
            "D": ["E"],
        }.get(name, []))

        graph = await build_dependency_graph(client, ["A"], max_depth=2)

        assert "A" in graph
        assert "B" in graph
        assert "C" in graph
        assert "D" not in graph

    @pytest.mark.asyncio
    async def test_build_dependency_graph_handles_errors(self):
        """Should gracefully handle inspect errors."""
        client = AsyncMock()
        client.get_dependencies = AsyncMock(side_effect=Exception("symbol not found"))

        graph = await build_dependency_graph(client, ["X"], max_depth=1)

        assert "X" in graph
        assert graph["X"] == []

    @pytest.mark.asyncio
    async def test_rank_symbols_basic(self):
        dep_graph = {
            "myDef": ["helper1", "helper2"],
            "helper1": ["common"],
            "helper2": ["common"],
            "common": [],
        }
        mock_client = AsyncMock()
        mock_client.inspect_symbol = AsyncMock(return_value={"module": "test"})
        ranked = await rank_symbols(["myDef"], dep_graph, mock_client)
        names = [s.name for s in ranked]

        assert "myDef" in names
        assert "common" in names

    @pytest.mark.asyncio
    async def test_rank_symbols_filters_structural_noise_when_relevance_predicate_is_used(self):
        dep_graph = {
            "myDef": ["Nat", "helper"],
            "Nat": [],
            "helper": [],
        }
        mock_client = AsyncMock()
        mock_client.inspect_symbol = AsyncMock(side_effect=lambda name: {
            "myDef": {"name": "myDef", "module": "test", "type": {"pp": "Nat"}},
            "Nat": {"name": "Nat", "module": "Init.Prelude", "inductInfo": {}, "type": {"pp": "Type"}},
            "helper": {"name": "helper", "module": "test", "type": {"pp": "Nat"}},
        }[name])
        ranked = await rank_symbols(["myDef"], dep_graph, mock_client, is_relevant=not_lean_internal)
        names = [s.name for s in ranked]

        assert "Nat" not in names
        assert "helper" in names
        assert "myDef" in names

    @pytest.mark.asyncio
    async def test_rank_symbols_empty(self):
        mock_client = AsyncMock()
        assert await rank_symbols([], {}, mock_client) == []


# ---------------------------------------------------------------------------
# Tactic pool tests
# ---------------------------------------------------------------------------

class TestTacticPool:
    def test_build_with_lemmas(self):
        """Should generate closers, openers, and per-lemma tactics."""
        lemmas = ["Nat.add_comm", "Nat.add_assoc", "Nat.mul_comm"]
        pool = build_tactic_pool(lemmas, user_constants=["myDef"])
        names = [wt.tactic for wt in pool]

        assert "grind" in names
        assert "simp_all" in names
        assert "constructor <;> expose_names" in names

        for lem in lemmas:
            assert f"apply {lem}" in names
            assert f"rw [{lem}]" in names

        assert any("simp only [" in t for t in names)

    def test_build_no_lemmas(self):
        """Should still produce closers and openers when no lemmas are available."""
        pool = build_tactic_pool([])
        names = [wt.tactic for wt in pool]

        assert "grind" in names
        assert "constructor <;> expose_names" in names
        assert not any("apply " in t for t in names)
        assert not any("rw [" in t for t in names)

    def test_deduplication(self):
        """Should not contain duplicate tactics."""
        pool = build_tactic_pool(["lem1", "lem2"])
        tactic_names = [wt.tactic for wt in pool]
        assert len(tactic_names) == len(set(tactic_names))


class TestLemmaFiltering:
    @pytest.mark.asyncio
    async def test_filter_lemmas_excludes_prop_valued_defs(self):
        client = AsyncMock()
        info_map = {
            "Foo.propDef": {"name": "Foo.propDef", "module": "Mathlib.Foo", "type": {"pp": "True"}},
            "Foo.realTheorem": {"name": "Foo.realTheorem", "module": "Mathlib.Foo", "type": {"pp": "x = x"}},
            "Foo.realLemma": {"name": "Foo.realLemma", "module": "Mathlib.Foo", "type": {"pp": "P ↔ P"}},
        }
        client.inspect_symbol = AsyncMock(side_effect=lambda name: info_map[name])

        results = [
            LeanExploreResult(
                name="Foo.propDef",
                statement="def Foo.propDef : True := trivial",
                source_file="Foo.lean",
                decl_type="definition",
            ),
            LeanExploreResult(
                name="Foo.realTheorem",
                statement="theorem Foo.realTheorem (x : Nat) : x = x := by rfl",
                source_file="Foo.lean",
                decl_type="theorem",
            ),
            LeanExploreResult(
                name="Foo.realLemma",
                statement="lemma Foo.realLemma (P : Prop) : P ↔ P := by rfl",
                source_file="Foo.lean",
                decl_type="theorem",
            ),
        ]

        filtered = await filter_lemmas(results, client, select=TopNSelector(10))

        assert [r.name for r in filtered] == ["Foo.realTheorem", "Foo.realLemma"]
        client.inspect_symbol.assert_any_call("Foo.realTheorem")
        client.inspect_symbol.assert_any_call("Foo.realLemma")
        assert client.inspect_symbol.await_count == 2

    @pytest.mark.asyncio
    async def test_filter_lemmas_keeps_non_lean_theorems_with_old_junk_prefixes(self):
        client = AsyncMock()
        client.inspect_symbol = AsyncMock(return_value={
            "name": "PUnit.ext",
            "module": "Init.Ext",
            "type": {"pp": "x = y ↔ True"},
        })

        results = [
            LeanExploreResult(
                name="PUnit.ext",
                statement="theorem PUnit.ext : x = y := by cases x; cases y; rfl",
                source_file="Init/Ext.lean",
                decl_type="theorem",
            ),
        ]

        filtered = await filter_lemmas(results, client, select=TopNSelector(10))

        assert [r.name for r in filtered] == ["PUnit.ext"]

    @pytest.mark.asyncio
    async def test_filter_lemmas_prefers_decl_type_over_statement_text(self):
        client = AsyncMock()
        client.inspect_symbol = AsyncMock(return_value={
            "name": "Foo.actualTheorem",
            "module": "Mathlib.Foo",
            "type": {"pp": "x = x"},
        })

        results = [
            LeanExploreResult(
                name="Foo.actualTheorem",
                statement="def Foo.actualTheorem : True := trivial",
                source_file="Foo.lean",
                decl_type="theorem",
            ),
        ]

        filtered = await filter_lemmas(results, client, select=TopNSelector(10))

        assert [r.name for r in filtered] == ["Foo.actualTheorem"]

    @pytest.mark.asyncio
    async def test_filter_lemmas_drops_when_print_header_says_def(self):
        client = AsyncMock()
        client.inspect_symbol = AsyncMock(return_value={
            "name": "Foo.mislabeled",
            "module": "Mathlib.Foo",
            "type": {"pp": "True"},
            "print_result": "def Foo.mislabeled : True :=\ntrivial",
        })

        results = [
            LeanExploreResult(
                name="Foo.mislabeled",
                statement="theorem Foo.mislabeled : True := by trivial",
                source_file="Foo.lean",
                decl_type="theorem",
            ),
        ]

        filtered = await filter_lemmas(results, client, select=TopNSelector(10))

        assert filtered == []

    @pytest.mark.asyncio
    async def test_filter_lemmas_drops_lean_internal_theorems(self):
        client = AsyncMock()
        client.inspect_symbol = AsyncMock(return_value={
            "name": "Lean.AssocList.cons.inj",
            "module": "Mathlib.Foo",
            "type": {"pp": "xs = ys ↔ a = b"},
        })

        results = [
            LeanExploreResult(
                name="Lean.AssocList.cons.inj",
                statement="theorem Lean.AssocList.cons.inj : xs = ys ↔ a = b := by sorry",
                source_file="Lean/Data/AssocList.lean",
                decl_type="theorem",
                module_name="Lean.Data.AssocList",
            ),
        ]

        filtered = await filter_lemmas(results, client, select=TopNSelector(10))

        assert filtered == []


# ---------------------------------------------------------------------------
# ProofSearchMCTS tests
# ---------------------------------------------------------------------------

class TestProofSearchMCTS:
    def _make_goal_state(self, goals=None, solved=False):
        """Create a mock GoalState."""
        gs = MagicMock(spec_set=["goals", "is_solved", "state_id", "messages", "_sentinel"])
        if solved:
            gs.goals = []
            gs.is_solved = True
        else:
            if goals is None:
                goal = MagicMock()
                goal.target = "∀ x : Nat, x = x"
                goal.variables = []
                goals = [goal]
            gs.goals = goals
            gs.is_solved = False
        gs.state_id = random.randint(1, 1000)
        gs.messages = []
        gs._sentinel = []
        return gs

    def test_search_result_dataclass(self):
        """ProofSearchResult should hold all expected fields."""
        result = ProofSearchResult(
            success=True,
            steps=5,
            duration=1.23,
        )
        assert result.success
        assert result.steps == 5
        assert result.duration == 1.23

    def test_search_result_defaults(self):
        """ProofSearchResult defaults should be sensible."""
        result = ProofSearchResult(success=False)
        assert not result.success
        assert result.steps == 0
        assert result.duration == 0.0

    def test_search_state_solved(self):
        """SearchState.is_solved should work for solved goals."""
        gs_solved = self._make_goal_state(solved=True)
        node = SearchState(
            goal_state=gs_solved, parent=None,
            parent_goal_id=None, priorities=[],
        )
        assert node.is_solved

    def test_next_tactic_respects_tested(self):
        """Should not return a tactic that has already been tested."""
        client = AsyncMock()
        agent = ProofSearchMCTS(
            tactic_pool=_wt(["rfl", "omega", "simp_all"]),
            pantograph_client=client,
        )
        result = agent._next_tactic(tested=["rfl", "omega", "simp_all"])
        assert result is None

    def test_next_tactic_selects_from_pool(self):
        """Should select tactics from the pool, excluding tested ones."""
        client = AsyncMock()
        agent = ProofSearchMCTS(
            tactic_pool=_wt(["rfl", "constructor <;> expose_names", "omega", "assumption"]),
            pantograph_client=client,
        )

        random.seed(42)
        choices = {agent._next_tactic(tested=[]) for _ in range(100)}
        assert "rfl" in choices
        assert "omega" in choices

    @pytest.mark.asyncio
    async def test_search_solved_immediately(self):
        """If the goal is already solved, search should return immediately."""
        server = AsyncMock()
        server.run_async = AsyncMock(return_value={'rootHasMVar': False})

        client = AsyncMock()
        client.get_server = AsyncMock(return_value=server)

        gs = self._make_goal_state(solved=True)
        agent = ProofSearchMCTS(tactic_pool=_wt(["rfl"]), pantograph_client=client)
        result = await agent.search(gs, max_steps=10)

        assert result.success
        assert result.steps == 0

    @pytest.mark.asyncio
    async def test_search_finds_proof_in_one_step(self):
        """Search should find a proof when a single tactic solves the goal."""
        server = AsyncMock()
        solved_gs = self._make_goal_state(solved=True)
        server.goal_tactic_async = AsyncMock(return_value=solved_gs)
        server.run_async = AsyncMock(return_value={'rootHasMVar': False})

        client = AsyncMock()
        client.get_server = AsyncMock(return_value=server)
        client.check_inductive = AsyncMock(return_value=(False, False))

        agent = ProofSearchMCTS(
            tactic_pool=_wt(["rfl"]),
            pantograph_client=client,
        )
        result = await agent.search(self._make_goal_state(), max_steps=10)

        assert result.success

    @pytest.mark.asyncio
    async def test_search_handles_tactic_failure(self):
        """Search should handle TacticFailure and try other tactics."""
        server = AsyncMock()
        solved_gs = self._make_goal_state(solved=True)
        server.goal_tactic_async = AsyncMock(
            side_effect=[TacticFailure("failed"), solved_gs],
        )
        server.run_async = AsyncMock(return_value={'rootHasMVar': False})

        client = AsyncMock()
        client.get_server = AsyncMock(return_value=server)
        client.check_inductive = AsyncMock(return_value=(False, False))

        agent = ProofSearchMCTS(
            tactic_pool=_wt(["bad_tactic", "rfl"]),
            pantograph_client=client,
        )
        result = await agent.search(self._make_goal_state(), max_steps=20)
        assert result.success

    @pytest.mark.asyncio
    async def test_search_exhaustion(self):
        """Search should give up after exhausting all tactics."""
        server = AsyncMock()
        server.goal_tactic_async = AsyncMock(side_effect=TacticFailure("always fails"))

        client = AsyncMock()
        client.get_server = AsyncMock(return_value=server)
        client.check_inductive = AsyncMock(return_value=(False, False))

        agent = ProofSearchMCTS(
            tactic_pool=_wt(["bad1", "bad2"]),
            pantograph_client=client,
        )
        result = await agent.search(self._make_goal_state(), max_steps=50)
        assert not result.success


# ---------------------------------------------------------------------------
# ProofSearcher orchestrator tests
# ---------------------------------------------------------------------------

class TestProofSearcher:
    @pytest.mark.asyncio
    async def test_build_pool_no_constants(self):
        """build_tactic_pool with no constants should produce structural tactics."""
        client = AsyncMock()
        searcher = ProofSearcher(client)
        searcher.tactic_pool = build_tactic_pool([])
        assert len(searcher.tactic_pool) > 0

    @pytest.mark.asyncio
    async def test_full_pipeline_with_constants(self):
        """Standalone functions should discover, rank, find lemmas, and build pool."""
        client = AsyncMock()
        client.discover_user_constants = AsyncMock(
            return_value=(["myDef"], ["myDef"], []),
        )
        client.get_dependencies = AsyncMock(return_value=["helper"])
        client.inspect_symbol = AsyncMock(return_value={
            "module": "Init", "type": {"pp": "myDef = 0"},
        })

        mock_lem = MagicMock()
        mock_lem.name = "Nat.add_comm"
        with patch(
            "tools.proof_search.discover_lemmas",
            new_callable=AsyncMock,
            return_value=[mock_lem],
        ):
            new, user_c, user_ctors = await client.discover_user_constants("test_key", "def myDef := 0")
            dep_graph = await build_dependency_graph(client, new)
            ranked = await rank_symbols(new, dep_graph, client, is_relevant=not_lean_internal)
            discovery_cfg = LemmaDiscoveryConfig()
            selector = TopNSelector()
            raw_lemmas = await discover_lemmas(ranked, config=discovery_cfg)
            filtered = await filter_lemmas(raw_lemmas, client, select=selector)
            pool = build_tactic_pool([r.name for r in filtered], user_c, user_ctors)

        assert len(pool) > 10

    @pytest.mark.asyncio
    async def test_search_delegates_to_mcts(self):
        """search() should load sorry from Goal, then run MCTS."""
        solved_gs = MagicMock()
        solved_gs.goals = []
        solved_gs.is_solved = True
        solved_gs.state_id = 1
        solved_gs.messages = []
        solved_gs._sentinel = []

        server = AsyncMock()
        server.run_async = AsyncMock(return_value={'rootHasMVar': False})

        client = AsyncMock()
        client.get_server = AsyncMock(return_value=server)
        client.check_inductive = AsyncMock(return_value=(False, False))
        client.load_sorry = AsyncMock(return_value=solved_gs)

        searcher = ProofSearcher(client)
        searcher.tactic_pool = _wt(["rfl"])

        goal = Goal(name="test", params=[], final_goal="True")
        result = await searcher.search(goal, max_steps=10)
        assert result.success
        client.load_sorry.assert_called_once_with(goal.as_sorried())


# ---------------------------------------------------------------------------
# Tactic recovery tests
# ---------------------------------------------------------------------------

class TestTacticRecovery:
    def _mk_goal_state(self, solved: bool = False):
        gs = MagicMock(spec_set=["goals", "is_solved", "state_id", "messages", "_sentinel"])
        gs.goals = [] if solved else [MagicMock(target="True", variables=[])]
        gs.is_solved = solved
        gs.state_id = random.randint(1, 1000)
        gs.messages = []
        gs._sentinel = []
        return gs

    def test_recover_tactics_prefers_cached_path(self):
        result = ProofSearchResult(
            success=True,
            _recovered_tactics=["intro", "rfl"],
        )
        tactics = result.recover_tactics()
        assert tactics == ["intro", "rfl"]
        # returns a copy
        assert tactics is not result._recovered_tactics

        proof = result.tactic_proof("theorem t : True := by\n  sorry")
        assert proof is not None
        assert "intro" in proof and "rfl" in proof

    def test_recover_tactics_requires_cached_path(self):
        root = SearchState(
            goal_state=self._mk_goal_state(solved=False),
            parent=None,
            parent_goal_id=None,
            priorities=[0.0],
        )
        child = SearchState(
            goal_state=self._mk_goal_state(solved=True),
            parent=root,
            parent_goal_id=0,
            priorities=[],
        )

        result = ProofSearchResult(success=True, _solved_node=child, _recovered_tactics=None)
        assert result.recover_tactics() is None

    @pytest.mark.asyncio
    async def test_search_validated_tactic_proof(self):
        client = AsyncMock()
        searcher = ProofSearcher(client)

        goal = Goal(name="g", params=[], final_goal="True")
        fake_result = ProofSearchResult(success=True, _recovered_tactics=["trivial"])

        with patch.object(searcher, "search", AsyncMock(return_value=fake_result)):
            ok_build = MagicMock(typechecks=True)
            client.check_build = AsyncMock(return_value=ok_build)

            validated = await searcher.search_validated_tactic_proof(goal)
            assert validated.search_result.success
            assert validated.tactic_proof is not None
            assert "trivial" in validated.tactic_proof
            assert validated.build_result is ok_build
            assert validated.status == ValidatedTacticProofStatus.VERIFIED

            bad_build = MagicMock(typechecks=False)
            client.check_build = AsyncMock(return_value=bad_build)
            validated2 = await searcher.search_validated_tactic_proof(goal)
            assert validated2.search_result.success
            assert validated2.tactic_proof is not None
            assert validated2.build_result is bad_build
            assert validated2.status == ValidatedTacticProofStatus.BUILD_FAILED

    @pytest.mark.asyncio
    async def test_search_validated_tactic_proof_recovery_failed_signal(self):
        client = AsyncMock()
        searcher = ProofSearcher(client)

        goal = Goal(name="g", params=[], final_goal="True")
        fake_result = ProofSearchResult(success=True, _recovered_tactics=None, _solved_node=None)
        client.check_build = AsyncMock()

        with patch.object(searcher, "search", AsyncMock(return_value=fake_result)):
            validated = await searcher.search_validated_tactic_proof(goal)
            assert validated.search_result.success
            assert validated.tactic_proof is None
            assert validated.build_result is None
            assert validated.status == ValidatedTacticProofStatus.RECOVERY_FAILED
            client.check_build.assert_not_called()


# ---------------------------------------------------------------------------
# Structural relevance tests
# ---------------------------------------------------------------------------

class TestStructuralRelevance:
    def test_typeclass_projection_detection(self):
        assert _is_typeclass_projection(
            "HAdd.hAdd",
            "{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ",
        )
        assert _is_typeclass_projection(
            "Membership.mem",
            "{α : outParam (Type u)} → {γ : Type v} → [self : Membership α γ] → γ → α → Prop",
        )
        assert not _is_typeclass_projection(
            "Nat.add_comm",
            "∀ (n m : Nat), n + m = m + n",
        )

    def test_not_lean_internal_rejects_inductives(self):
        assert not not_lean_internal({
            "name": "Nat",
            "module": "Init.Prelude",
            "inductInfo": {"ctors": ["Nat.zero", "Nat.succ"]},
            "type": {"pp": "Type"},
        })

    def test_not_lean_internal_rejects_instance_like_symbols(self):
        assert not not_lean_internal({
            "name": "instDecidableEqNat",
            "module": "Init.Prelude",
            "type": {"pp": "DecidableEq Nat"},
        })

    def test_not_lean_internal_rejects_generic_operator_heads(self):
        assert not not_lean_internal({
            "name": "HAdd.hAdd",
            "module": "Init.Prelude",
            "type": {"pp": "{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ"},
        })

    def test_not_lean_internal_keeps_regular_theorems(self):
        assert not_lean_internal({
            "name": "Nat.add_comm",
            "module": "Init.Data.Nat.Basic",
            "type": {"pp": "∀ (n m : Nat), n + m = m + n"},
        })
