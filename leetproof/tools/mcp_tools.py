"""MCP (Model Context Protocol) tools integration for LLoom agents."""

import asyncio
from typing import List, Optional
from langchain_mcp_tools import convert_mcp_to_langchain_tools

from logging_config import get_logger

logger = get_logger(__name__)

LEAN_LSP_MCP_VERSION =  "0.17.0"

LEAN_DIAGNOSTICS = "lean_diagnostic_messages"  # Essential: Check compilation errors
LEAN_GOAL = "lean_goal"                 # Essential: Inspect proof goals
LEAN_HOVER = "lean_hover_info"           # Essential: Understand types and docs
LEAN_FILE_OUTLINE = "lean_file_outline"         # Useful: See file structure
LEAN_FINDER = "lean_leanfinder"          # Useful: Semantic search for theorems
LEAN_STATE_SEARCH = "lean_state_search"        # Useful: Goal-based theorem search
class MCPToolsManager:
    """Manages MCP server connections and tools."""

    def __init__(self):
        self.tools = []
        self.cleanup_func = None
        self._initialized = False

    async def initialize(self, mcp_servers: dict):
        """Initialize MCP tools from server configurations.

        Args:
            mcp_servers: Dictionary of MCP server configurations.
                Example:
                {
                    "lean-lsp": {
                        "command": "lean-lsp-mcp",
                        "args": ["--workspace", "/path/to/lean/project"]
                    }
                }
        """
        if self._initialized:
            logger.warning("MCP tools already initialized")
            return

        logger.info(f"Initializing MCP tools from {len(mcp_servers)} server(s)")
        try:
            self.tools, self.cleanup_func = await convert_mcp_to_langchain_tools(
                mcp_servers
            )
            self._initialized = True
            logger.info(f"Successfully initialized {len(self.tools)} MCP tools")
            for tool in self.tools:
                # logger.info(f"  - {tool.name}: {tool.description}")
                logger.info(f"  - {tool.name}")
        except Exception as e:
            logger.error(f"Failed to initialize MCP tools: {e}")
            raise

    async def cleanup(self):
        """Cleanup MCP server connections."""
        if self.cleanup_func:
            logger.info("Cleaning up MCP connections")
            try:
                await self.cleanup_func()
            except Exception:
                # Suppress errors during cleanup - they're usually harmless generator cleanup issues
                pass
            finally:
                self._initialized = False

    def get_tools(self) -> list:
        """Get the list of initialized MCP tools.

        Returns:
            List of LangChain-compatible tools
        """
        if not self._initialized:
            logger.warning("MCP tools not initialized yet")
            return []
        return self.tools


# Global instance for easy access
_mcp_manager: Optional[MCPToolsManager] = None
_cached_tools: Optional[list] = None
_cached_lean_lsp_tools : Optional[list] = None

async def get_lean_lsp_tool(tool_name: str):
    return (await get_lean_lsp_tools([tool_name]))[0]

async def get_lean_lsp_tools(allowed_tool_names: List[str]) -> list:
    """Get Lean LSP MCP tools.

    Returns:
        List of Lean LSP tools for use with LangChain agents.
        Only returns the most useful tools for proof conversion to avoid distractions.
    """
    global _mcp_manager
    global _cached_lean_lsp_tools


    if _mcp_manager is None:
        _mcp_manager = MCPToolsManager()

        lean_lsp_package = f"lean-lsp-mcp@v{LEAN_LSP_MCP_VERSION}"
        logger.info(f"Using lean-lsp-mcp version: {LEAN_LSP_MCP_VERSION}")

        mcp_servers = {
            "lean-lsp": {
                "command": "uvx",
                "args": [lean_lsp_package]
            }
        }

        await _mcp_manager.initialize(mcp_servers)

    # Get all tools (cache this)
    if _cached_lean_lsp_tools is None:
        _cached_lean_lsp_tools = _mcp_manager.get_tools()

    # Filter from cache based on requested tool names
    filtered_tools = [tool for tool in _cached_lean_lsp_tools if tool.name in allowed_tool_names]

    if filtered_tools:
        logger.info(f"Filtered Lean LSP tools to {len(filtered_tools)}/{len(_cached_lean_lsp_tools)}: {[t.name for t in filtered_tools]}")

    return filtered_tools


async def get_all_tools() -> list:
     """Get all tools (common + MCP tools) with caching.

     This is a shared helper for agents to get all available tools.
     Tools are cached after first load to avoid reinitializing MCP.

     Returns:
         List of all available tools
     """
     global _cached_tools

     if _cached_tools is None:
         from tools.common import COMMON_TOOLS
         logger.info("Loading all tools (common + MCP)...")
         mcp_tools = await get_lean_lsp_tools([])
         _cached_tools = COMMON_TOOLS + mcp_tools
         logger.info(f"Loaded {len(_cached_tools)} tools: {[t.name for t in _cached_tools]}")

     return _cached_tools


async def cleanup_mcp():
    """Cleanup global MCP manager."""
    global _mcp_manager
    if _mcp_manager:
        await _mcp_manager.cleanup()
        _mcp_manager = None


_event_loop = None

def get_lean_lsp_tools_sync() -> list:
    """
    Synchronous wrapper for get_lean_lsp_tools.
    Creates and maintains a persistent event loop to avoid cleanup issues.
    """
    global _event_loop

    if _event_loop is None:
        _event_loop = asyncio.new_event_loop()
        asyncio.set_event_loop(_event_loop)
        logger.info("Created new event loop for MCP tools")

    return _event_loop.run_until_complete(get_lean_lsp_tools([]))


def cleanup_mcp_sync():
    """Synchronous cleanup for MCP connections."""
    global _event_loop, _mcp_manager

    if _mcp_manager and _event_loop:
        try:
            logger.info("Cleaning up MCP connections synchronously")

            # Cancel all pending tasks first
            pending = asyncio.all_tasks(_event_loop)
            for task in pending:
                task.cancel()

            # Run cleanup
            _event_loop.run_until_complete(cleanup_mcp())

            # Wait for any remaining tasks to finish cancellation
            if pending:
                _event_loop.run_until_complete(asyncio.gather(*pending, return_exceptions=True))

            # Close the loop
            _event_loop.close()
            _event_loop = None
        except Exception as e:
            logger.warning(f"Error during MCP cleanup (this is usually harmless): {e}")
