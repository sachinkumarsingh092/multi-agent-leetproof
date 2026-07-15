from utils.shutdown import (
    ShutdownHookMode,
    clear_shutdown_hooks,
    shutdown_hook,
    _run_shutdown_hooks,
)


def test_shutdown_hook_runs_nested_scopes_in_lifo_order():
    calls: list[str] = []
    clear_shutdown_hooks()

    with shutdown_hook(ShutdownHookMode.CLEAR_AND_PUSH, lambda: calls.append("outer")):
        with shutdown_hook(ShutdownHookMode.PUSH, lambda: calls.append("inner")):
            _run_shutdown_hooks()

    clear_shutdown_hooks()
    assert calls == ["inner", "outer"]


def test_shutdown_hook_clear_and_push_restores_previous_scopes_after_exit():
    calls: list[str] = []
    clear_shutdown_hooks()

    with shutdown_hook(ShutdownHookMode.PUSH, lambda: calls.append("base")):
        with shutdown_hook(ShutdownHookMode.CLEAR_AND_PUSH, lambda: calls.append("replacement")):
            _run_shutdown_hooks()
        _run_shutdown_hooks()

    clear_shutdown_hooks()
    assert calls == ["replacement", "base"]
