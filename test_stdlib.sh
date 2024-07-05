#!/bin/bash

for file in $(find stdlib_tests -name "*.mjl"); do
    cargo run -- interpret ${file}
    if [[ $? -ne 0 ]]; then
        echo "Test failed: ${file}"
        exit 1
    fi
done
