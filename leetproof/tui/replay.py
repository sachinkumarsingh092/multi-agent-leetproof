"""TUI replay - view saved session state."""
import argparse
import sys
import re
from pathlib import Path

from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll, HorizontalScroll, Container
from textual.widgets import Static, Header, Footer, RichLog, ProgressBar, Input, Label
from textual.reactive import reactive
from textual.binding import Binding
from textual.screen import ModalScreen
from textual import events
from textual.message import Message

from tui.snapshot import TUISnapshot


def format_tokens(n: int) -> str:
    """Format token count with K/M suffixes."""
    if n >= 1_000_000:
        return f"{n/1_000_000:.1f}M"
    elif n >= 10_000:
        return f"{n/1_000:.1f}K"
    elif n >= 1_000:
        return f"{n/1_000:.2f}K"
    return str(n)


def clean_agent_name(name: str) -> str:
    """Clean agent name for display (remove prefixes, format nicely)."""
    name = name.replace("velvet_", "").replace("lloom_", "")
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
  [bold]e[/]             Jump to first error
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
  [bold]q[/]             Quit
""", classes="help-content"),
            id="help-container"
        )

    def on_click(self, event: events.Click) -> None:
        self.dismiss()


class SearchBar(Static):
    """Search bar widget for log filtering."""

    class SearchChanged(Message):
        def __init__(self, query: str) -> None:
            self.query = query
            super().__init__()

    class SearchClosed(Message):
        pass

    class SearchSubmitted(Message):
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
        self.post_message(self.SearchSubmitted())


class FilterBar(Static):
    """Log level filter bar."""

    class FilterChanged(Message):
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


class ReplayStatusPanel(Static):
    """Panel showing session status."""

    def __init__(self, snapshot: TUISnapshot):
        super().__init__()
        self.snapshot = snapshot

    def compose(self) -> ComposeResult:
        yield Static("SESSION INFO", classes="panel-title")
        with HorizontalScroll(classes="scrollable-content"):
            yield Static(id="status-content")

    def on_mount(self) -> None:
        lines = []

        # Status with color and duration
        status = self.snapshot.status
        if status.upper() == "COMPLETED":
            status_line = f"[green]●[/] {status}"
        elif status.upper() == "FAILED":
            status_line = f"[red]✖[/] {status}"
        else:
            status_line = f"[yellow]◆[/] {status}"

        # Add duration if available
        if self.snapshot.elapsed_seconds > 0:
            elapsed = self.snapshot.elapsed_seconds
            hours, remainder = divmod(int(elapsed), 3600)
            minutes, secs = divmod(remainder, 60)
            if hours > 0:
                duration = f"{hours:02d}:{minutes:02d}:{secs:02d}"
            else:
                duration = f"{minutes:02d}:{secs:02d}"
            status_line += f"  [cyan]{duration}[/]"

        lines.append(status_line)

        # Parameters (full values, no truncation)
        for key, value in self.snapshot.params.items():
            lines.append(f"{key}: {value}")

        if self.snapshot.error:
            lines.append("")
            lines.append(f"[red]Error: {self.snapshot.error}[/]")

        self.query_one("#status-content", Static).update("\n".join(lines))


class ReplayTokenPanel(Static):
    """Panel showing token usage."""

    def __init__(self, snapshot: TUISnapshot):
        super().__init__()
        self.snapshot = snapshot

    def compose(self) -> ComposeResult:
        yield Static("TOKENS", classes="panel-title")
        with HorizontalScroll(classes="scrollable-content"):
            yield Static(id="token-content")
        yield ProgressBar(id="token-progress", total=100, show_eta=False)

    def on_mount(self) -> None:
        t = self.snapshot.tokens

        lines = []
        # Compact format
        inp = format_tokens(t.input_tokens)
        out = format_tokens(t.output_tokens)
        total = format_tokens(t.total_tokens)
        lines.append(f"↓ {inp}  ↑ {out}  = {total}")

        # Cache info if there are cache hits
        if t.cache_read_tokens > 0:
            cache_fmt = format_tokens(t.cache_read_tokens)
            cache_pct = int((t.cache_read_tokens / t.input_tokens) * 100) if t.input_tokens > 0 else 0
            lines.append(f"[green]⚡ Cache: {cache_fmt} ({cache_pct}%)[/]")

        # Cost if available
        if t.cost_usd > 0:
            lines.append(f"[yellow]💰 ${t.cost_usd:.4f}[/]")

        lines.append(f"LLM Calls: {t.call_count}")

        # Limits if set
        if t.max_total and t.max_total > 0:
            pct = min(100, int((t.total_tokens / t.max_total) * 100))
            lines.append(f"Limit: {format_tokens(t.max_total)} ({pct}%)")

        self.query_one("#token-content", Static).update("\n".join(lines))

        # Update progress bar
        progress_bar = self.query_one("#token-progress", ProgressBar)
        if t.max_total and t.max_total > 0:
            pct = min(100, int((t.total_tokens / t.max_total) * 100))
            progress_bar.update(progress=pct)
            progress_bar.display = True
        else:
            progress_bar.display = False


class ReplayAgentPanel(Static):
    """Panel showing per-agent breakdown."""

    def __init__(self, snapshot: TUISnapshot):
        super().__init__()
        self.snapshot = snapshot

    def compose(self) -> ComposeResult:
        yield Static("PER-AGENT", classes="panel-title")
        with VerticalScroll(classes="scrollable-content", id="agent-scroll"):
            yield Static(id="agent-content")

    def on_mount(self) -> None:
        lines = []
        for name, usage in sorted(self.snapshot.agent_usage.items()):
            # Clean agent name (no truncation)
            display_name = clean_agent_name(name)
            inp_fmt = format_tokens(usage.prompt_tokens)
            out_fmt = format_tokens(usage.completion_tokens)
            lines.append(f"{display_name} ({usage.call_count})")
            # Show cache info if there are cache hits
            if usage.cache_read_tokens > 0:
                cache_fmt = format_tokens(usage.cache_read_tokens)
                cache_pct = int((usage.cache_read_tokens / usage.prompt_tokens) * 100) if usage.prompt_tokens > 0 else 0
                lines.append(f"  ↓ {inp_fmt}  ↑ {out_fmt}  [green]⚡{cache_fmt} ({cache_pct}%)[/]")
            else:
                lines.append(f"  ↓ {inp_fmt}  ↑ {out_fmt}")

        self.query_one("#agent-content", Static).update("\n".join(lines) if lines else "[dim](no agent data)[/]")


class ColoredLog(RichLog):
    """Log widget with colored output based on log level."""

    def write_line(self, line: str) -> None:
        """Write a line with color based on log level."""
        from rich.text import Text
        styled_text = self._colorize_line(line)
        self.write(styled_text)

    def _colorize_line(self, line: str):
        """Apply color based on log level. Returns Rich Text object."""
        from rich.text import Text

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

            return text

        # Return plain text (Text constructor doesn't interpret markup)
        return Text(line, no_wrap=False)


class ReplayTUI(App):
    """TUI for replaying saved session state."""

    CSS = """
    Screen {
        layout: horizontal;
    }

    #sidebar {
        width: 40;
        height: 100%;
        border: solid $accent;
        padding: 1;
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

    ReplayStatusPanel, ReplayTokenPanel, ReplayAgentPanel {
        height: auto;
        margin-bottom: 1;
        padding-bottom: 1;
        border-bottom: dashed $surface-lighten-2;
    }

    ReplayAgentPanel {
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

    /* Position indicator */
    #position-indicator {
        dock: bottom;
        height: 1;
        background: $surface;
        text-align: right;
        padding: 0 1;
        color: $text-muted;
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
        Binding("question_mark", "show_help", "Help"),
        Binding("p", "toggle_params", "Params"),
        Binding("slash", "open_search", "Search"),
        Binding("n", "next_match", "Next"),
        Binding("N", "prev_match", "Prev", key_display="shift+n"),
        Binding("escape", "close_search", "Close", show=False),
        Binding("e", "jump_to_error", "Error"),
        Binding("1", "toggle_debug", "Debug", show=False),
        Binding("2", "toggle_info", "Info", show=False),
        Binding("3", "toggle_warning", "Warning", show=False),
        Binding("4", "toggle_error", "Error", show=False),
        Binding("0", "clear_filters", "All", show=False),
        Binding("j", "scroll_down", "Down"),
        Binding("k", "scroll_up", "Up"),
        Binding("g", "scroll_top", "Top"),
        Binding("G", "scroll_bottom", "Bottom"),
        Binding("pageup", "page_up", "PgUp", show=False),
        Binding("pagedown", "page_down", "PgDn", show=False),
    ]

    def __init__(self, snapshot: TUISnapshot, session_name: str):
        super().__init__()
        self.snapshot = snapshot
        self.session_name = session_name
        self._log_widget = None
        self._search_bar = None
        self._filter_bar = None
        self._status_panel = None
        self._position_indicator = None

        # All logs and filtered state
        self._all_logs = snapshot.logs.copy()
        self._active_filters: set = set()
        self._search_query = ""
        self._search_matches: list[int] = []
        self._current_match = 0

        # Find first error line for jump-to-error
        self._first_error_line = -1
        for i, line in enumerate(self._all_logs):
            if "| ERROR |" in line or "| CRITICAL |" in line:
                self._first_error_line = i
                break

    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)
        with Horizontal():
            with Vertical(id="sidebar"):
                yield ReplayStatusPanel(self.snapshot)
                yield ReplayTokenPanel(self.snapshot)
                yield ReplayAgentPanel(self.snapshot)
            with Vertical(id="log-container"):
                yield FilterBar()
                yield SearchBar()
                yield ColoredLog(id="log-output", highlight=True, auto_scroll=False, markup=True)
                yield Static("", id="position-indicator")
        yield Footer()

    def on_mount(self) -> None:
        self.title = f"LLoom Replay"
        self.sub_title = f"{self.session_name} - {len(self.snapshot.logs)} lines"

        self._log_widget = self.query_one("#log-output", ColoredLog)
        self._search_bar = self.query_one(SearchBar)
        self._filter_bar = self.query_one(FilterBar)
        self._status_panel = self.query_one(ReplayStatusPanel)
        self._position_indicator = self.query_one("#position-indicator", Static)

        # Load all logs
        self._refresh_logs()
        self._update_position()

    def _should_show_line(self, line: str) -> bool:
        """Check if line should be shown based on active filters."""
        if not self._active_filters:
            return True

        match = re.match(r'^\d{2}:\d{2}:\d{2}\s*\|\s*(\w+)\s*\|', line)
        if match:
            level = match.group(1).upper()
            if level == "WARN":
                level = "WARNING"
            return level in self._active_filters

        return True

    def _refresh_logs(self) -> None:
        """Refresh log display based on current filters."""
        if self._log_widget:
            self._log_widget.clear()
            for line in self._all_logs:
                if self._should_show_line(line):
                    self._log_widget.write_line(line)

    def _update_position(self) -> None:
        """Update position indicator."""
        if self._position_indicator and self._log_widget:
            total = len(self._all_logs)
            # Approximate current position
            if total > 0:
                self._position_indicator.update(f"Lines: {total}")

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

    def _goto_match(self) -> None:
        """Scroll to current search match."""
        if self._search_matches and self._log_widget:
            if self._search_bar:
                self._search_bar.update_match_count(self._current_match + 1, len(self._search_matches))

            match_line = self._search_matches[self._current_match]
            total_lines = len(self._all_logs)
            if total_lines > 0:
                scroll_pct = match_line / total_lines
                self._log_widget.scroll_to(y=int(scroll_pct * self._log_widget.virtual_size.height))

    # Action handlers
    def action_show_help(self) -> None:
        """Show help screen."""
        self.push_screen(HelpScreen())

    def action_toggle_params(self) -> None:
        """Toggle status panel visibility."""
        if self._status_panel:
            self._status_panel.display = not self._status_panel.display

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

    def action_jump_to_error(self) -> None:
        """Jump to first error in logs."""
        if self._first_error_line >= 0 and self._log_widget:
            total_lines = len(self._all_logs)
            if total_lines > 0:
                scroll_pct = self._first_error_line / total_lines
                self._log_widget.scroll_to(y=int(scroll_pct * self._log_widget.virtual_size.height))
                self.notify(f"Jumped to first error at line {self._first_error_line + 1}")
        else:
            self.notify("No errors found in logs", severity="warning")

    def action_toggle_debug(self) -> None:
        if self._filter_bar:
            self._filter_bar.toggle_level("DEBUG")

    def action_toggle_info(self) -> None:
        if self._filter_bar:
            self._filter_bar.toggle_level("INFO")

    def action_toggle_warning(self) -> None:
        if self._filter_bar:
            self._filter_bar.toggle_level("WARNING")

    def action_toggle_error(self) -> None:
        if self._filter_bar:
            self._filter_bar.toggle_level("ERROR")

    def action_clear_filters(self) -> None:
        if self._filter_bar:
            self._filter_bar.clear_filters()

    def action_scroll_down(self) -> None:
        if self._log_widget:
            self._log_widget.scroll_down()

    def action_scroll_up(self) -> None:
        if self._log_widget:
            self._log_widget.scroll_up()

    def action_scroll_top(self) -> None:
        if self._log_widget:
            self._log_widget.scroll_home()

    def action_scroll_bottom(self) -> None:
        if self._log_widget:
            self._log_widget.scroll_end()

    def action_page_up(self) -> None:
        if self._log_widget:
            self._log_widget.scroll_page_up()

    def action_page_down(self) -> None:
        if self._log_widget:
            self._log_widget.scroll_page_down()

    # Message handlers
    def on_search_bar_search_changed(self, event: SearchBar.SearchChanged) -> None:
        self._search_query = event.query
        self._update_search()

    def on_search_bar_search_closed(self, event: SearchBar.SearchClosed) -> None:
        self._search_query = ""
        self._search_matches = []

    def on_search_bar_search_submitted(self, event: SearchBar.SearchSubmitted) -> None:
        self.action_next_match()

    def on_filter_bar_filter_changed(self, event: FilterBar.FilterChanged) -> None:
        self._active_filters = event.levels
        self._refresh_logs()


def main():
    """Entry point for TUI replay."""
    parser = argparse.ArgumentParser(description="Replay a saved LLoom session")
    parser.add_argument(
        "session_dir",
        type=str,
        help="Path to session directory (e.g. .sessions/2025-01-15_10-30-00)"
    )
    args = parser.parse_args()

    # Find session directory
    session_path = Path(args.session_dir)
    if not session_path.exists():
        print(f"Error: Session directory not found: {session_path.absolute()}")
        sys.exit(1)

    state_file = session_path / "tui_state.json"
    if not state_file.exists():
        print(f"Error: No TUI state found in session: {session_path}")
        print(f"Expected file: {state_file}")
        sys.exit(1)

    # Load and display
    try:
        snapshot = TUISnapshot.load(session_path)
        session_name = session_path.name
        app = ReplayTUI(snapshot, session_name)
        app.run()
    except Exception as e:
        print(f"Error loading session: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
