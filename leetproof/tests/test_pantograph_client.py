import asyncio
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

import pytest

from tools.pantograph_client import PantographClient
from utils.lean.constants import PANTOGRAPH_CORE_OPTIONS
from utils.lean.types import LakeBuildResult, LeanDiagnostic


@pytest.mark.asyncio
async def test_is_grindable_true_when_no_errors():
    client = PantographClient(project_path=".", imports=["Init"], options={}, core_options=PANTOGRAPH_CORE_OPTIONS)
    try:
        with patch.object(client, "_check_compile", new=AsyncMock(return_value=[])) as mock_check:
            ok = await client.is_grindable("Foo.bar")

            assert ok is True
            mock_check.assert_awaited_once_with(
                "attribute [grind] Foo.bar",
                diagnostics_severity=["error"],
            )
    finally:
        client.close()


@pytest.mark.asyncio
async def test_is_grindable_false_when_error_present():
    client = PantographClient(project_path=".", imports=["Init"], options={}, core_options=PANTOGRAPH_CORE_OPTIONS)
    try:
        with patch.object(
            client,
            "_check_compile",
            new=AsyncMock(
                return_value=[
                    LeanDiagnostic(
                        severity="error",
                        message="invalid E-matching theorem",
                        line=1,
                        column=1,
                    )
                ]
            ),
        ) as mock_check:
            ok = await client.is_grindable("Foo.mk")

            assert ok is False
            mock_check.assert_awaited_once_with(
                "attribute [grind] Foo.mk",
                diagnostics_severity=["error"],
            )
    finally:
        client.close()


@pytest.mark.asyncio
async def test_is_grindable_rejects_empty_name_without_compile_check():
    client = PantographClient(project_path=".", imports=["Init"], options={}, core_options=PANTOGRAPH_CORE_OPTIONS)
    try:
        with patch.object(client, "_check_compile", new=AsyncMock(return_value=[])) as mock_check:
            assert await client.is_grindable("") is False
            assert await client.is_grindable("   ") is False

            mock_check.assert_not_awaited()
    finally:
        client.close()


def test_parse_printed_declaration_extracts_kind():
    parsed = PantographClient._parse_printed_declaration(
        "@[defeq] protected theorem PUnit.ext.{u} : ∀ (x y : PUnit), x = y :=\nfun x y => rfl"
    )

    assert parsed == "@[defeq] protected theorem PUnit.ext.{u} : ∀ (x y : PUnit), x = y :=\nfun x y => rfl"


@pytest.mark.asyncio
async def test_inspect_symbol_attaches_print_result():
    client = PantographClient(project_path=".", imports=["Init"], options={}, core_options=PANTOGRAPH_CORE_OPTIONS)
    try:
        with patch.object(
            client,
            "_get_server_unlocked",
            new=AsyncMock(),
        ) as mock_get_server, patch.object(
            client,
            "check_build",
            new=AsyncMock(
                return_value=LakeBuildResult(
                    typechecks=True,
                    diagnostics=[
                        LeanDiagnostic(
                            severity="info",
                            message="def List.length.{u} : {α : Type u} → List α → Nat :=\nfun xs => 0",
                            line=1,
                            column=1,
                        )
                    ],
                )
            ),
        ) as mock_check_build:
            server = AsyncMock()
            server.env_inspect_async = AsyncMock(
                return_value={"module": "Init.Data.List.Basic", "type": {"pp": "List α → Nat"}}
            )
            mock_get_server.return_value = server

            info = await client.inspect_symbol("List.length")

            assert info is not None
            assert info["print_result"] == "def List.length.{u} : {α : Type u} → List α → Nat :=\nfun xs => 0"
            server.env_inspect_async.assert_awaited_once_with(
                "List.length",
                print_value=True,
                print_dependency=True,
            )
            mock_check_build.assert_awaited_once_with(
                "#print List.length",
                include_info_logs=True,
            )
    finally:
        client.close()


@pytest.mark.asyncio
async def test_get_server_proxy_serializes_direct_server_calls():
    client = PantographClient(project_path=".", imports=["Init"], options={}, core_options=PANTOGRAPH_CORE_OPTIONS)
    try:
        active_calls = 0
        max_active_calls = 0

        class FakeServer:
            def __init__(self):
                self.proc = SimpleNamespace(returncode=None)

            async def goal_tactic_async(self, *args, **kwargs):
                nonlocal active_calls, max_active_calls
                active_calls += 1
                max_active_calls = max(max_active_calls, active_calls)
                await asyncio.sleep(0.01)
                active_calls -= 1
                return {"args": args, "kwargs": kwargs}

        with patch.object(client, "_start_server", new=AsyncMock(return_value=FakeServer())) as mock_start:
            server = await client.get_server()
            await asyncio.gather(
                server.goal_tactic_async("goal-a", "tactic-a"),
                server.goal_tactic_async("goal-b", "tactic-b"),
            )

            assert max_active_calls == 1
            mock_start.assert_awaited_once()
    finally:
        client.close()
