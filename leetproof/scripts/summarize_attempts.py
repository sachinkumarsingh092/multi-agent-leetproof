

import argparse
from collections import Counter, defaultdict
from utils.analytics.velvet_programmer import query_attempt_meta as programmer_query_attempt_meta
from utils.analytics.velvet_invariant_inferrer import query_attempt_meta as  inferrer_query_attempt_meta
from utils.analytics.spec_generation import query_attempt_meta as  specgen_query_attempt_meta
from utils.analytics.lean_synth_and_verify import query_attempt_meta as lean_synth_query_attempt_meta


def get_meta_summary(session_name: str):
    programmer_attempts = programmer_query_attempt_meta(session_name)
    inferrer_attempts = inferrer_query_attempt_meta(session_name)
    spec_attempts = specgen_query_attempt_meta(session_name)
    lean_synth_attempts = lean_synth_query_attempt_meta(session_name)

    mp = {
        "Spec Generation Summary" : {
            "attempts": spec_attempts
        },
        "Programmer Summary" : {
            "attempts": programmer_attempts
        },
        "Inferrer Summary" : {
            "attempts": inferrer_attempts
        },
        "Lean Synth Summary" : {
            "attempts": lean_synth_attempts
        }
    }

    for summary, v in mp.items():
        print("=" * 80)
        print(summary)
        print("=" * 80)
        attempts = v["attempts"]
        mapping = defaultdict(lambda: [])
        for attempt in attempts:
            mapping[attempt.payload.final_outcome].append(str(attempt.attempt_no))
        for k,v in mapping.items():
            attempt_nos_with_k = ", ".join(v)
            print(f"{k}   : {len(v)} [{attempt_nos_with_k}]")


def main():
    parser = argparse.ArgumentParser(description="Summarize attempts for a specific session")
    parser.add_argument("session_name", type=str, help="Name of the session to summarize")
    
    args = parser.parse_args()
    get_meta_summary(args.session_name)

if __name__ == '__main__':
    main()


