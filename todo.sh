#!/bin/sh

# List todos and holes in Agda files.
echo "Hole (admit) count:"
find . -name "*.agda" -print0 | xargs -0 grep "admit _" -c | grep -v ":0"
echo "TODO list:"
find . -name "*.agda" -print0 | xargs -0 grep "TODO:"
