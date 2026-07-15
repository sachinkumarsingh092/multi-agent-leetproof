"""LLM provider configuration and instance management.

Provides LLMConfig (provider + model) and ReasoningLevel for provider-agnostic
reasoning/thinking configuration. Instances are cached by (provider, model, level).
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from langchain_core.language_models import BaseChatModel

from logging_config import get_logger

logger = get_logger(__name__)


# ---------------------------------------------------------------------------
# Public types
# ---------------------------------------------------------------------------

class ReasoningLevel(Enum):
    """Provider-agnostic reasoning/thinking level.

    Maps to:
    - Anthropic: thinking budget_tokens
    - OpenAI: reasoning effort
    - Google: thinking_budget
    """
    NONE = "none"
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"


@dataclass(frozen=True)
class LLMConfig:
    """Immutable LLM configuration — provider + model name."""
    provider: str
    model: str


# ---------------------------------------------------------------------------
# Provider-specific reasoning parameters
# ---------------------------------------------------------------------------

# Anthropic thinking budget (tokens) per reasoning level.
# budget_tokens counts towards max_tokens, so max_tokens must be larger.
_ANTHROPIC_THINKING = {
    ReasoningLevel.LOW:    {"budget_tokens": 2000,  "max_tokens": 8192},
    ReasoningLevel.MEDIUM: {"budget_tokens": 8000,  "max_tokens": 16384},
    ReasoningLevel.HIGH:   {"budget_tokens": 16000, "max_tokens": 32768},
}

# Gemini thinking budget per reasoning level.
# ChatGoogleGenerativeAI exposes thinking_budget / include_thoughts rather than a
# generic "thinking_level" knob, so we map our abstract reasoning levels here.
_GOOGLE_THINKING = {
    ReasoningLevel.LOW: 2000,
    ReasoningLevel.MEDIUM: 8000,
    ReasoningLevel.HIGH: 16000,
}


def require_env(var: str):
    """Verify that a required API key environment variable is set."""
    import os
    if not os.environ.get(var):
        raise RuntimeError(
            f"Environment variable {var} is not set. "
            f"Export it before running: export {var}=<your-key>"
        )


def _create_llm(provider: str, model: str, reasoning: ReasoningLevel = ReasoningLevel.NONE) -> BaseChatModel:
    """Create a LangChain chat model for the given provider, model, and reasoning level.

    This is the internal factory — callers should use get_llm() which caches.
    """
    from utils.token_tracker import get_token_tracker

    provider = provider.lower()
    token_tracker = get_token_tracker()

    if provider == "openai":
        require_env("OPENAI_API_KEY")
        try:
            from langchain_openai import ChatOpenAI
        except ImportError:
            raise ImportError(
                "langchain-openai package not installed. "
                "Install with: pip install langchain-openai"
            )
        from typing import Dict, Any
        # Use plain chat completions: OpenAI-compatible endpoints like
        # DigitalOcean inference don't serve all models via /v1/responses,
        # and the Responses-API "reasoning" kwarg is not supported there.
        kwargs: Dict[str, Any] = {
            "max_tokens": 8192,
        }
        return ChatOpenAI(model_name=model, callbacks=[token_tracker], **kwargs)

    elif provider == "google":
        require_env("GOOGLE_API_KEY")
        try:
            from langchain_google_genai import ChatGoogleGenerativeAI
        except ImportError:
            raise ImportError(
                "langchain-google-genai package not installed. "
                "Install with: pip install langchain-google-genai"
            )
        kwargs = {}
        if reasoning != ReasoningLevel.NONE:
            kwargs["thinking_budget"] = _GOOGLE_THINKING[reasoning]
        return ChatGoogleGenerativeAI(model=model, callbacks=[token_tracker], **kwargs)

    elif provider == "anthropic":
        require_env("ANTHROPIC_API_KEY")
        try:
            from langchain_anthropic import ChatAnthropic
        except ImportError:
            raise ImportError(
                "langchain-anthropic package not installed. "
                "Install with: pip install langchain-anthropic"
            )
        kwargs = {}
        kwargs["betas"] = ["extended-cache-ttl-2025-04-11"]
        if reasoning != ReasoningLevel.NONE:
            cfg = _ANTHROPIC_THINKING[reasoning]
            kwargs["thinking"] = {"type": "enabled", "budget_tokens": cfg["budget_tokens"]}
            kwargs["max_tokens"] = cfg["max_tokens"]
            kwargs["temperature"] = 1  # Required when thinking is enabled
        return ChatAnthropic(model_name=model, stop=None, callbacks=[token_tracker], **kwargs)

    else:
        raise ValueError(
            f"Unsupported provider: {provider}. "
            f"Supported providers: openai, google, anthropic"
        )


# ---------------------------------------------------------------------------
# Instance cache
# ---------------------------------------------------------------------------

_llm_cache: dict[tuple[str, str, str], BaseChatModel] = {}


def get_llm(config: LLMConfig, reasoning: ReasoningLevel = ReasoningLevel.NONE) -> BaseChatModel:
    """Get a (cached) LLM instance for the given config and reasoning level.

    Instances are cached by (provider, model, reasoning_level) — calling this
    multiple times with the same arguments returns the same object.
    """
    cache_key = (config.provider, config.model, reasoning.value)
    if cache_key not in _llm_cache:
        logger.info(f"Creating LLM: {config.provider}/{config.model} (reasoning={reasoning.value})")
        _llm_cache[cache_key] = _create_llm(config.provider, config.model, reasoning)
    return _llm_cache[cache_key]
