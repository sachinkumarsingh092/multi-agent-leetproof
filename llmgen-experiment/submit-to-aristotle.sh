LLOOM=${LLOOM:-uv run --project ../lloom/ lloom-agent}
# Default values
TARGET_DIR="./llmgen/problems/"
FILE_PATTERN="*/*Impl.lean"

# Parse named parameters
while [[ "$#" -gt 0 ]]; do
    case $1 in
        --dir|-d) TARGET_DIR="$2"; shift ;;
        --pattern|-p) FILE_PATTERN="$2"; shift ;;
        *) echo "Unknown parameter passed: $1"; exit 1 ;;
    esac
    shift
done

echo "Using LLoom command: $LLOOM"
echo "Searching in directory: $TARGET_DIR"
echo "Using file pattern: $FILE_PATTERN"

for file in $(${LLOOM} get-sorried-files "$TARGET_DIR" --sections-to-show Specs --proof-status sorried --file-pattern "$FILE_PATTERN" --json | jq -r '.[].file'); do
    python3 -c "from pathlib import Path; import sys; f = Path(sys.argv[1]); exit(len([p for p in Path(f.parent).rglob(f.stem + '*' + f.suffix) if p.stem.endswith('AristotleProof') ]))" $file 
    if [ $? -eq 0 ]; then
        echo "$file hasn't been submitted to aristotle, submitting now"
        $LLOOM aristotle-submit --project . --mode sorries $file
    fi
done
