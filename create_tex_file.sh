#!/bin/bash

# Check for the correct number of arguments
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <file.tla>"
    exit 1
fi

# Extract the filename without the extension
BASENAME=$(basename -- "$1")
FILENAME="${BASENAME%.*}"
EXTENSION="${BASENAME##*.}"

# Check if the file has the .tla extension
if [ "$EXTENSION" != "tla" ]; then
    echo "Error: Provide a .tla file as an argument."
    exit 1
fi

# Create a temporary file
TMPFILE=$(mktemp --suffix=.tla XXXXXXXX)

# Set a trap to remove the temporary file on EXIT
trap 'rm -f "$TMPFILE" "${TMPFILE%.tla}.log" "${TMPFILE%.tla}.dvi" "${TMPFILE%.tla}.aux"' EXIT

# Remove the generated TLA+ section from the TLA file
sed '/\* BEGIN TRANSLATION/,/\* END TRANSLATION/d' "$1" > "$TMPFILE"

# Generate the .tex file
if java -cp tla2tools.jar tla2tex.TLA -shade -noPcalShade -nops "$TMPFILE"; then
    # Rename the temporary .tex file to match the original filename
    mv "${TMPFILE%.*}.tex" "${FILENAME}.tex"
    echo "Processed $1 and generated ${FILENAME}.tex"
else
    echo "Error: Failed to generate the .tex file."
    exit 1
fi
