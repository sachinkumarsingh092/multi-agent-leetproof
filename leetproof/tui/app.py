"""Main Textual TUI application for LLoom Agent."""
from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll, HorizontalScroll, Container
from textual.widgets import Static, Header, Footer, RichLog, ProgressBar, Input, Label
from textual.reactive import reactive
from textual.binding import Binding
from textual.screen import ModalScreen
from textual import events
from textual.message import Message
from rich.text import Text
from rich.style import Style
from typing import Optional
from pathlib import Path
import time
import re


# Log level colors
LEVEL_STYLES = {
    "DEBUG": Style(color="bright_black"),
    "INFO": Style(color="white"),
    "WARNING": Style(color="yellow"),
    "WARN": Style(color="yellow"),
    "ERROR": Style(color="red", bold=True),
    "CRITICAL": Style(color="red", bold=True, reverse=True),
}


def format_tokens(n: int) -> str:
    """Format token count with K/M suffixes."""
    if n >= 1_000_000:
        return f"{n/1_000_000:.1f}M"
    elif n >= 10_000:
        return f"{n/1_000:.1f}K"
    elif n >= 1_000:
        return f"{n/1_000:.2f}K"
    return str(n)


def format_elapsed(seconds: float) -> str:
    """Format elapsed time as HH:MM:SS."""
    hours, remainder = divmod(int(seconds), 3600)
    minutes, secs = divmod(remainder, 60)
    if hours > 0:
        return f"{hours:02d}:{minutes:02d}:{secs:02d}"
    return f"{minutes:02d}:{secs:02d}"


def clean_agent_name(name: str) -> str:
    """Clean agent name for display (remove prefixes, format nicely)."""
    # Remove common prefixes
    name = name.replace("velvet_", "").replace("lloom_", "")
    # Convert snake_case to Title Case
    name = name.replace("_", " ").title()
    return name


class HelpScreen(ModalScreen):
    """Help overlay showing keybindings."""

    BINDINGS = [
        Binding("escape", "dismiss", "Close"),
        Binding("?", "dismiss", "Close"),
        Binding("q", "dismiss", "Close"),
    ]

    def compose(self) -> ComposeResult:
        yield Container(
            Static("KEYBOARD SHORTCUTS", classes="help-title"),
            Static("""
[bold cyan]Navigation[/]
  [bold]j / k[/]         Scroll down / up
  [bold]g / G[/]         Go to top / bottom
  [bold]PgUp / PgDn[/]   Page up / down

[bold cyan]Search & Filter[/]
  [bold]/[/]             Open search
  [bold]n / N[/]         Next / previous match
  [bold]Escape[/]        Close search
  [bold]1[/]             Toggle DEBUG logs
  [bold]2[/]             Toggle INFO logs
  [bold]3[/]             Toggle WARNING logs
  [bold]4[/]             Toggle ERROR logs
  [bold]0[/]             Show all levels

[bold cyan]Display[/]
  [bold]p[/]             Toggle parameters panel
  [bold]?[/]             Show this help

[bold cyan]Clipboard[/]
  [bold]c[/]             Copy logs to clipboard

[bold cyan]General[/]
  [bold]q / Ctrl+C[/]    Quit
""", classes="help-content"),
            id="help-container"
        )

    def on_click(self, event: events.Click) -> None:
        self.dismiss()


class SearchBar(Static):
    """Search bar widget for log filtering."""

    class SearchChanged(Message):
        """Message sent when search query changes."""
        def __init__(self, query: str) -> None:
            self.query = query
            super().__init__()

    class SearchClosed(Message):
        """Message sent when search is closed."""
        pass

    class SearchSubmitted(Message):
        """Message sent when Enter is pressed in search."""
        pass

    def compose(self) -> ComposeResult:
        yield Label("Search: ", id="search-label")
        yield Input(placeholder="Type to search...", id="search-input")
        yield Static("", id="match-count")

    def on_mount(self) -> None:
        self.display = False

    def show(self) -> None:
        self.display = True
        self.query_one("#search-input", Input).focus()

    def hide(self) -> None:
        self.display = False
        self.query_one("#search-input", Input).value = ""
        self.post_message(self.SearchClosed())

    def update_match_count(self, current: int, total: int) -> None:
        if total > 0:
            self.query_one("#match-count", Static).update(f" {current}/{total} matches")
        else:
            self.query_one("#match-count", Static).update(" No matches")

    def on_input_changed(self, event: Input.Changed) -> None:
        self.post_message(self.SearchChanged(event.value))

    def on_input_submitted(self, event: Input.Submitted) -> None:
        # Enter key triggers next match
        self.post_message(self.SearchSubmitted())


class FilterBar(Static):
    """Log level filter bar."""

    class FilterChanged(Message):
        """Message sent when filters change."""
        def __init__(self, levels: set) -> None:
            self.levels = levels
            super().__init__()

    active_levels: reactive[set] = reactive(set)  # type: ignore[assignment]

    def compose(self) -> ComposeResult:
        yield Static("Filters: ", id="filter-label")
        yield Static("", id="filter-status")

    def on_mount(self) -> None:
        self._update_display()

    def watch_active_levels(self, levels: set) -> None:
        self._update_display()
        self.post_message(self.FilterChanged(levels))

    def _update_display(self) -> None:
        if not self.active_levels:
            status = "[dim]All levels[/]"
        else:
            parts = []
            for level in ["DEBUG", "INFO", "WARNING", "ERROR"]:
                if level in self.active_levels:
                    color = "bright_black" if level == "DEBUG" else "white" if level == "INFO" else "yellow" if level == "WARNING" else "red"
                    parts.append(f"[{color}]{level}[/]")
            status = " ".join(parts)
        self.query_one("#filter-status", Static).update(status)

    def toggle_level(self, level: str) -> None:
        levels = set(self.active_levels)
        if level in levels:
            levels.discard(level)
        else:
            levels.add(level)
        self.active_levels = levels

    def clear_filters(self) -> None:
        self.active_levels = set()


class StatusPanel(Static):
    """Panel showing current agent status, file, and elapsed time."""

    agent_name = reactive("Initializing...")
    status = reactive("Starting")
    current_file = reactive("")
    llm_calls = reactive(0)
    elapsed_seconds = reactive(0.0)
    status_color = reactive("green")

    def compose(self) -> ComposeResult:
        yield Static("STATUS", classes="panel-title")
        with HorizontalScroll(classes="scrollable-content"):
            yield Static(id="status-content")

    def on_mount(self) -> None:
        self._update_all()

    def watch_agent_name(self, value: str) -> None:
        self._update_all()

    def watch_status(self, value: str) -> None:
        self._update_all()

    def watch_current_file(self, value: str) -> None:
        self._update_all()

    def watch_llm_calls(self, value: int) -> None:
        self._update_all()

    def watch_elapsed_seconds(self, value: float) -> None:
        self._update_all()

    def _update_all(self) -> None:
        try:
            lines = []

            # Status line with color and elapsed time
            elapsed = format_elapsed(self.elapsed_seconds)
            status_indicator = "●" if self.status.lower() in ("running", "starting") else "◆" if self.status.lower() == "completed" else "✖"
            color = "green" if self.status.lower() in ("running", "starting") else "cyan" if self.status.lower() == "completed" else "red"
            lines.append(f"[{color}]{status_indicator}[/] {self.status}  [{color}]{elapsed}[/]")

            # Agent name (full, no truncation)
            display_name = clean_agent_name(self.agent_name)
            lines.append(f"Agent: {display_name}")

            # LLM calls
            lines.append(f"LLM Calls: {self.llm_calls}")

            # Current file (full path, scrollable)
            if self.current_file:
                lines.append(f"File: {self.current_file}")

            self.query_one("#status-content", Static).update("\n".join(lines))
        except Exception:
            pass


class TokenPanel(Static):
    """Panel showing token usage with rates."""

    input_tokens = reactive(0)
    output_tokens = reactive(0)
    total_tokens = reactive(0)
    max_input = reactive(0)
    max_output = reactive(0)
    max_total = reactive(0)
    cache_read_tokens = reactive(0)
    cache_write_tokens = reactive(0)
    cost_usd = reactive(0.0)
    tokens_per_minute = reactive(0.0)

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self._start_time = time.time()
        self._last_total = 0

    def compose(self) -> ComposeResult:
        yield Static("TOKENS", classes="panel-title")
        with HorizontalScroll(classes="scrollable-content"):
            yield Static(id="token-content")
        yield ProgressBar(id="token-progress", total=100, show_eta=False)

    def on_mount(self) -> None:
        self._update_displays()

    def watch_input_tokens(self, value: int) -> None:
        self._update_displays()

    def watch_output_tokens(self, value: int) -> None:
        self._update_displays()

    def watch_total_tokens(self, value: int) -> None:
        self._update_rate()
        self._update_displays()

    def watch_max_input(self, value: int) -> None:
        self._update_displays()

    def watch_max_output(self, value: int) -> None:
        self._update_displays()

    def watch_max_total(self, value: int) -> None:
        self._update_displays()

    def watch_cache_read_tokens(self, value: int) -> None:
        self._update_displays()

    def watch_cost_usd(self, value: float) -> None:
        self._update_displays()

    def _update_rate(self) -> None:
        """Calculate tokens per minute."""
        elapsed = time.time() - self._start_time
        if elapsed > 0:
            self.tokens_per_minute = (self.total_tokens / elapsed) * 60

    def _format_limit(self, used: int, limit: int) -> str:
        """Format as 'used/limit' or 'used' if unlimited."""
        formatted_used = format_tokens(used)
        if limit and limit > 0:
            formatted_limit = format_tokens(limit)
            return f"{formatted_used}/{formatted_limit}"
        return formatted_used

    def _update_displays(self) -> None:
        try:
            lines = []

            # Compact format: ↓ input  ↑ output  = total
            inp = format_tokens(self.input_tokens)
            out = format_tokens(self.output_tokens)
            total = format_tokens(self.total_tokens)
            lines.append(f"↓ {inp}  ↑ {out}  = {total}")

            # Cache info if there are cache hits
            if self.cache_read_tokens > 0:
                cache_fmt = format_tokens(self.cache_read_tokens)
                cache_pct = int((self.cache_read_tokens / self.input_tokens) * 100) if self.input_tokens > 0 else 0
                lines.append(f"[green]⚡ Cache: {cache_fmt} ({cache_pct}%)[/]")

            # Cost if available
            if self.cost_usd > 0:
                lines.append(f"[yellow]💰 ${self.cost_usd:.4f}[/]")

            # Rate
            rate = format_tokens(int(self.tokens_per_minute))
            lines.append(f"Rate: {rate}/min")

            # Limits if set
            if self.max_total and self.max_total > 0:
                pct = min(100, int((self.total_tokens / self.max_total) * 100))
                lines.append(f"Limit: {format_tokens(self.max_total)} ({pct}%)")

            self.query_one("#token-content", Static).update("\n".join(lines))

            # Progress bar
            progress_bar = self.query_one("#token-progress", ProgressBar)
            if self.max_total and self.max_total > 0:
                pct = min(100, int((self.total_tokens / self.max_total) * 100))
                progress_bar.update(progress=pct)
                progress_bar.display = True
            else:
                progress_bar.display = False
        except Exception:
            pass


class AgentTokensPanel(Static):
    """Panel showing per-agent token breakdown."""

    def compose(self) -> ComposeResult:
        yield Static("PER-AGENT", classes="panel-title")
        with VerticalScroll(classes="scrollable-content", id="agent-scroll"):
            yield Static(id="agent-tokens-list")

    def update_agents(self, agent_tokens: dict) -> None:
        """Update the per-agent token display."""
        try:
            lines = []
            for agent, usage in sorted(agent_tokens.items()):
                inp = usage.get("prompt_tokens", 0)
                out = usage.get("completion_tokens", 0)
                calls = usage.get("call_count", 0)
                cache_read = usage.get("cache_read_tokens", 0)
                # Clean agent name (no truncation)
                display_name = clean_agent_name(agent)
                # Format tokens compactly
                inp_fmt = format_tokens(inp)
                out_fmt = format_tokens(out)
                lines.append(f"{display_name} ({calls})")
                # Show cache info if there are cache hits
                if cache_read > 0:
                    cache_fmt = format_tokens(cache_read)
                    cache_pct = int((cache_read / inp) * 100) if inp > 0 else 0
                    lines.append(f"  ↓ {inp_fmt}  ↑ {out_fmt}  [green]⚡{cache_fmt} ({cache_pct}%)[/]")
                else:
                    lines.append(f"  ↓ {inp_fmt}  ↑ {out_fmt}")

            display = "\n".join(lines) if lines else "[dim](no calls yet)[/]"
            self.query_one("#agent-tokens-list", Static).update(display)
        except Exception:
            pass


class ParamsPanel(Static):
    """Panel showing run parameters (toggleable)."""

    def __init__(self, params: dict, **kwargs):
        super().__init__(**kwargs)
        self.params = params

    def compose(self) -> ComposeResult:
        yield Static("PARAMETERS [dim](press 'p' to hide)[/]", classes="panel-title")
        with VerticalScroll(classes="scrollable-content", id="params-scroll"):
            yield Static(id="params-list")

    def on_mount(self) -> None:
        lines = []
        for key, value in self.params.items():
            # No truncation - full values
            lines.append(f"{key}: {value}")
        self.query_one("#params-list", Static).update("\n".join(lines))


class ColoredLog(RichLog):
    """Log widget with colored output based on log level."""

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self._search_query: str = ""

    def set_search_query(self, query: str) -> None:
        """Set the search query for highlighting."""
        self._search_query = query

    def write_line(self, line: str) -> None:
        """Write a line with color based on log level."""
        from rich.text import Text
        # Extract log level from line format: "HH:MM:SS | LEVEL | ..."
        styled_text = self._colorize_line(line)
        self.write(styled_text)

    def _colorize_line(self, line: str) -> Text:
        """Apply color based on log level. Returns Rich Text object."""
        from rich.text import Text

        # Match log format: "HH:MM:SS | LEVEL | module | message"
        match = re.match(r'^(\d{2}:\d{2}:\d{2})\s*\|\s*(\w+)\s*\|(.*)$', line)
        if match:
            timestamp, level, rest = match.groups()
            level_upper = level.strip().upper()

            text = Text()
            text.append(timestamp, style="bright_black")
            text.append(" | ")

            if level_upper == "DEBUG":
                text.append(level, style="bright_black")
            elif level_upper == "INFO":
                text.append(level, style="white")
            elif level_upper in ("WARNING", "WARN"):
                text.append(level, style="yellow")
            elif level_upper in ("ERROR", "CRITICAL"):
                text.append(level, style="red bold")
            else:
                text.append(level)

            text.append(" |")

            if level_upper in ("ERROR", "CRITICAL"):
                text.append(rest, style="red")
            else:
                text.append(rest)

            # Apply search highlighting if query is set
            if self._search_query:
                self._highlight_search(text)

            return text

        # Return plain text (Text constructor doesn't interpret markup)
        text = Text(line, no_wrap=False)
        if self._search_query:
            self._highlight_search(text)
        return text

    def _highlight_search(self, text: Text) -> None:
        """Highlight search matches in the text."""
        if not self._search_query:
            return
        # Case-insensitive highlighting
        text.highlight_words([self._search_query], style="black on yellow", case_sensitive=False)


class LLoomTUI(App):
    """Main TUI application for LLoom Agent."""

    CSS = """
    Screen {
        layout: horizontal;
    }

    #sidebar {
        width: 40;
        height: 100%;
        border: solid green;
        padding: 1;
        scrollbar-gutter: stable;
    }

    #log-container {
        width: 1fr;
        height: 100%;
        border: solid $primary;
    }

    .panel-title {
        text-style: bold;
        color: cyan;
        margin-bottom: 1;
    }

    StatusPanel, TokenPanel, AgentTokensPanel, ParamsPanel {
        height: auto;
        margin-bottom: 1;
        padding-bottom: 1;
        border-bottom: dashed $surface-lighten-2;
    }

    ParamsPanel {
        border-bottom: none;
    }

    .scrollable-content {
        height: auto;
        max-height: 10;
    }

    #agent-scroll {
        max-height: 8;
    }

    ProgressBar {
        margin-top: 1;
        padding: 0 1;
    }

    ColoredLog {
        height: 1fr;
        scrollbar-gutter: stable;
    }

    /* Search bar styling */
    SearchBar {
        dock: top;
        height: 3;
        background: $surface;
        border-bottom: solid $primary;
        padding: 0 1;
        layout: horizontal;
    }

    SearchBar #search-label {
        width: auto;
        padding: 1 0;
    }

    SearchBar #search-input {
        width: 1fr;
    }

    SearchBar #match-count {
        width: auto;
        padding: 1 0;
        color: $text-muted;
    }

    /* Filter bar styling */
    FilterBar {
        dock: top;
        height: 2;
        background: $surface;
        border-bottom: solid $surface-lighten-1;
        padding: 0 1;
        layout: horizontal;
    }

    FilterBar #filter-label {
        width: auto;
    }

    FilterBar #filter-status {
        width: 1fr;
    }

    /* Help screen styling */
    #help-container {
        width: 60;
        height: auto;
        max-height: 80%;
        background: $surface;
        border: solid $primary;
        padding: 1 2;
        margin: 2 4;
    }

    .help-title {
        text-style: bold;
        color: cyan;
        text-align: center;
        padding-bottom: 1;
        border-bottom: solid $primary;
        margin-bottom: 1;
    }

    .help-content {
        height: auto;
    }
    """

    BINDINGS = [
        Binding("q", "quit", "Quit"),
        Binding("ctrl+c", "quit", "Quit"),
        Binding("question_mark", "show_help", "Help"),
        Binding("p", "toggle_params", "Params"),
        Binding("slash", "open_search", "Search"),
        Binding("n", "next_match", "Next"),
        Binding("N", "prev_match", "Prev", key_display="shift+n"),
        Binding("escape", "close_search", "Close", show=False),
        Binding("1", "toggle_debug", "Debug", show=False),
        Binding("2", "toggle_info", "Info", show=False),
        Binding("3", "toggle_warning", "Warning", show=False),
        Binding("4", "toggle_error", "Error", show=False),
        Binding("0", "clear_filters", "All", show=False),
        Binding("j", "scroll_down", "Down", show=False),
        Binding("k", "scroll_up", "Up", show=False),
        Binding("g", "scroll_top", "Top", show=False),
        Binding("G", "scroll_bottom", "Bottom", show=False),
        Binding("pageup", "page_up", "PgUp", show=False),
        Binding("pagedown", "page_down", "PgDn", show=False),
    ]

    def __init__(self, params: Optional[dict] = None, **kwargs):
        super().__init__(**kwargs)
        self.params = params or {}
        self._status_panel: Optional[StatusPanel] = None
        self._token_panel: Optional[TokenPanel] = None
        self._agent_tokens_panel: Optional[AgentTokensPanel] = None
        self._params_panel: Optional[ParamsPanel] = None
        self._log_widget: Optional[ColoredLog] = None
        self._search_bar: Optional[SearchBar] = None
        self._filter_bar: Optional[FilterBar] = None
        self._start_time = time.time()
        self._timer = None

        # Search state
        self._all_logs: list[str] = []
        self._filtered_logs: list[str] = []
        self._search_matches: list[int] = []
        self._current_match: int = 0
        self._search_query: str = ""
        self._active_filters: set = set()

    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)
        with Horizontal():
            with VerticalScroll(id="sidebar"):
                yield StatusPanel()
                yield TokenPanel()
                yield AgentTokensPanel()
                yield ParamsPanel(self.params)
            with Vertical(id="log-container"):
                yield FilterBar()
                yield SearchBar()
                yield ColoredLog(id="log-output", highlight=True, auto_scroll=False, markup=True)
        yield Footer()

    def on_mount(self) -> None:
        self._status_panel = self.query_one(StatusPanel)
        self._token_panel = self.query_one(TokenPanel)
        self._agent_tokens_panel = self.query_one(AgentTokensPanel)
        self._params_panel = self.query_one(ParamsPanel)
        self._log_widget = self.query_one("#log-output", ColoredLog)
        self._search_bar = self.query_one(SearchBar)
        self._filter_bar = self.query_one(FilterBar)
        self.title = "LLoom Agent"
        self.sub_title = self.params.get("session", "")

        # Start elapsed time timer
        self._timer = self.set_interval(1.0, self._update_elapsed)

    def _update_elapsed(self) -> None:
        """Update elapsed time display."""
        if self._status_panel:
            elapsed = time.time() - self._start_time
            self._status_panel.elapsed_seconds = elapsed

    def update_status(self, agent_name: str, status: str, current_file: Optional[str] = None) -> None:
        """Update agent, status, and current file display."""
        if self._status_panel:
            self._status_panel.agent_name = agent_name
            self._status_panel.status = status
            self._status_panel.current_file = current_file or ""

    def update_llm_calls(self, count: int) -> None:
        """Update LLM call count display."""
        if self._status_panel:
            self._status_panel.llm_calls = count

    def update_agent(self, agent_name: str, status: str = "Running") -> None:
        """Update the current agent display (legacy method)."""
        self.update_status(agent_name, status, None)

    def update_tokens(
        self,
        input_tokens: int,
        output_tokens: int,
        total_tokens: int,
        max_input: Optional[int] = None,
        max_output: Optional[int] = None,
        max_total: Optional[int] = None,
        agent_tokens: Optional[dict] = None,
        cache_read_tokens: int = 0,
        cache_write_tokens: int = 0,
        cost_usd: float = 0.0,
    ) -> None:
        """Update token usage display."""
        if self._token_panel:
            self._token_panel.input_tokens = input_tokens
            self._token_panel.output_tokens = output_tokens
            self._token_panel.total_tokens = total_tokens
            self._token_panel.cache_read_tokens = cache_read_tokens
            self._token_panel.cache_write_tokens = cache_write_tokens
            self._token_panel.cost_usd = cost_usd
            if max_input is not None:
                self._token_panel.max_input = max_input
            if max_output is not None:
                self._token_panel.max_output = max_output
            if max_total is not None:
                self._token_panel.max_total = max_total

        if self._agent_tokens_panel and agent_tokens:
            self._agent_tokens_panel.update_agents(agent_tokens)

    def write_log(self, message: str) -> None:
        """Write a message to the log panel."""
        self._all_logs.append(message)

        # Check if line passes filters
        if self._should_show_line(message):
            if self._log_widget:
                # Check if we're at the bottom before writing
                at_bottom = self._log_widget.scroll_y >= self._log_widget.max_scroll_y - 5
                self._log_widget.write_line(message)
                # Only auto-scroll if we were at the bottom
                if at_bottom:
                    self._log_widget.scroll_end()

    def _should_show_line(self, line: str) -> bool:
        """Check if line should be shown based on active filters."""
        if not self._active_filters:
            return True

        # Extract level from line
        match = re.match(r'^\d{2}:\d{2}:\d{2}\s*\|\s*(\w+)\s*\|', line)
        if match:
            level = match.group(1).upper()
            if level == "WARN":
                level = "WARNING"
            return level in self._active_filters

        return True  # Show lines that don't match the format

    def _refresh_logs(self) -> None:
        """Refresh log display based on current filters."""
        if self._log_widget:
            # Check if we're at the bottom before refreshing
            at_bottom = self._log_widget.scroll_y >= self._log_widget.max_scroll_y - 5
            self._log_widget.clear()
            for line in self._all_logs:
                if self._should_show_line(line):
                    self._log_widget.write_line(line)
            # Only auto-scroll if we were at the bottom
            if at_bottom:
                self._log_widget.scroll_end()

    def _update_search(self) -> None:
        """Update search matches."""
        self._search_matches = []
        if self._search_query:
            query_lower = self._search_query.lower()
            for i, line in enumerate(self._all_logs):
                if query_lower in line.lower():
                    self._search_matches.append(i)

        self._current_match = 0
        if self._search_bar:
            total = len(self._search_matches)
            current = self._current_match + 1 if total > 0 else 0
            self._search_bar.update_match_count(current, total)

    # Action handlers
    def action_show_help(self) -> None:
        """Show help screen."""
        self.push_screen(HelpScreen())

    def action_toggle_params(self) -> None:
        """Toggle parameters panel visibility."""
        if self._params_panel:
            self._params_panel.display = not self._params_panel.display

    def action_open_search(self) -> None:
        """Open search bar."""
        if self._search_bar:
            self._search_bar.show()

    def action_close_search(self) -> None:
        """Close search bar."""
        if self._search_bar and self._search_bar.display:
            self._search_bar.hide()
            self._search_query = ""
            self._search_matches = []
            # Clear highlighting
            if self._log_widget:
                self._log_widget.set_search_query("")
                self._refresh_logs()

    def action_next_match(self) -> None:
        """Go to next search match."""
        if self._search_matches:
            self._current_match = (self._current_match + 1) % len(self._search_matches)
            self._goto_match()

    def action_prev_match(self) -> None:
        """Go to previous search match."""
        if self._search_matches:
            self._current_match = (self._current_match - 1) % len(self._search_matches)
            self._goto_match()

    def _goto_match(self) -> None:
        """Scroll to current search match."""
        if self._search_matches and self._log_widget:
            # Update match count display
            if self._search_bar:
                self._search_bar.update_match_count(self._current_match + 1, len(self._search_matches))

            # Scroll to approximate position
            match_line = self._search_matches[self._current_match]
            total_lines = len(self._all_logs)
            if total_lines > 0:
                # Calculate scroll position
                scroll_pct = match_line / total_lines
                self._log_widget.scroll_to(y=int(scroll_pct * self._log_widget.virtual_size.height))

    def action_toggle_debug(self) -> None:
        """Toggle DEBUG level filter."""
        if self._filter_bar:
            self._filter_bar.toggle_level("DEBUG")

    def action_toggle_info(self) -> None:
        """Toggle INFO level filter."""
        if self._filter_bar:
            self._filter_bar.toggle_level("INFO")

    def action_toggle_warning(self) -> None:
        """Toggle WARNING level filter."""
        if self._filter_bar:
            self._filter_bar.toggle_level("WARNING")

    def action_toggle_error(self) -> None:
        """Toggle ERROR level filter."""
        if self._filter_bar:
            self._filter_bar.toggle_level("ERROR")

    def action_clear_filters(self) -> None:
        """Clear all level filters."""
        if self._filter_bar:
            self._filter_bar.clear_filters()

    def action_scroll_down(self) -> None:
        """Scroll log down."""
        if self._log_widget:
            self._log_widget.scroll_down()

    def action_scroll_up(self) -> None:
        """Scroll log up."""
        if self._log_widget:
            self._log_widget.scroll_up()

    def action_scroll_top(self) -> None:
        """Scroll to top of log."""
        if self._log_widget:
            self._log_widget.scroll_home()

    def action_scroll_bottom(self) -> None:
        """Scroll to bottom of log."""
        if self._log_widget:
            self._log_widget.scroll_end()

    def action_page_up(self) -> None:
        """Page up in log."""
        if self._log_widget:
            self._log_widget.scroll_page_up()

    def action_page_down(self) -> None:
        """Page down in log."""
        if self._log_widget:
            self._log_widget.scroll_page_down()

    # Message handlers
    def on_search_bar_search_changed(self, event: SearchBar.SearchChanged) -> None:
        """Handle search query change."""
        self._search_query = event.query
        self._update_search()
        # Update highlighting and refresh logs
        if self._log_widget:
            self._log_widget.set_search_query(event.query)
            self._refresh_logs()

    def on_search_bar_search_closed(self, event: SearchBar.SearchClosed) -> None:
        """Handle search close."""
        self._search_query = ""
        self._search_matches = []
        # Clear highlighting (don't resume auto-scroll, user must press G)
        if self._log_widget:
            self._log_widget.set_search_query("")
            self._refresh_logs()

    def on_search_bar_search_submitted(self, event: SearchBar.SearchSubmitted) -> None:
        """Handle Enter in search - go to next match."""
        self.action_next_match()

    def on_filter_bar_filter_changed(self, event: FilterBar.FilterChanged) -> None:
        """Handle filter change."""
        self._active_filters = event.levels
        self._refresh_logs()

    async def action_quit(self) -> None:
        """Quit the application."""
        if self._timer:
            self._timer.stop()
        self.exit()


def build_params_dict() -> dict:
    """Build the params dict from command-line arguments."""
    try:
        from args import get_args
        args = get_args()
        params = {}

        # Core params - full values, no truncation
        if args.provider:
            params["provider"] = args.provider
        if args.model:
            params["model"] = args.model
        if args.session_name:
            params["session"] = args.session_name

        # File params - full paths
        if args.output_file:
            params["output"] = str(Path(args.output_file))
        if args.input_file:
            params["input"] = str(Path(args.input_file))

        # Limits and settings
        if args.recursion_limit:
            params["recursion"] = args.recursion_limit

        # Token limits (only show if set)
        if args.max_input_tokens:
            params["max_in"] = f"{args.max_input_tokens:,}"
        if args.max_output_tokens:
            params["max_out"] = f"{args.max_output_tokens:,}"
        if args.max_total_tokens:
            params["max_total"] = f"{args.max_total_tokens:,}"

        return params
    except Exception:
        return {}
