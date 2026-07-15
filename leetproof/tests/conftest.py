# -*- coding: utf-8 -*-
"""Pytest configuration - mock DBOS for unit testing.

For unit tests, we mock DBOS so we can test the actual logic
without workflow/checkpointing overhead.
"""

import sys
from unittest.mock import MagicMock


def _passthrough_decorator(*args, **kwargs):
    """Decorator that returns the function unchanged."""
    def decorator(func):
        return func
    # Handle both @decorator and @decorator() syntax
    if len(args) == 1 and callable(args[0]) and not kwargs:
        return args[0]
    return decorator


def _passthrough_class_decorator(*args, **kwargs):
    """Class decorator that returns the class unchanged."""
    def decorator(cls):
        return cls
    if len(args) == 1 and isinstance(args[0], type) and not kwargs:
        return args[0]
    return decorator


# Create mock before any test modules import dbos
class MockDBOS:
    """Mock DBOS that makes decorators no-ops."""
    workflow = staticmethod(_passthrough_decorator)
    step = staticmethod(_passthrough_decorator)
    dbos_class = staticmethod(_passthrough_class_decorator)

    @staticmethod
    def launch():
        pass

    @staticmethod
    def register_instance(inst):
        pass


class MockDBOSConfiguredInstance:
    """Mock base class that doesn't require DBOS registration."""
    def __init__(self, *args, config_name=None, **kwargs):
        self.config_name = config_name or self.__class__.__name__
        super().__init__(*args, **kwargs)


# Only patch if we're running tests and dbos isn't already imported
if "pytest" in sys.modules and "dbos" not in sys.modules:
    mock_dbos_module = MagicMock()
    mock_dbos_module.DBOS = MockDBOS
    mock_dbos_module.DBOSConfiguredInstance = MockDBOSConfiguredInstance
    mock_dbos_module.DBOSConfig = dict
    sys.modules["dbos"] = mock_dbos_module
