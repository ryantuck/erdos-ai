# Formalize Conjecture

To formalize conjecture NUM:

1. Read problem from `tidy/NUM.html`.
2. Formalize conjecture in lean and persist to `conjectures/NUM.lean`.
3. Build the file using the command `lake build conjectures/NUM.lean`.
4. Debug build until it runs successfully.

Things to consider:

- Note that build logs will throw warnings about sorry declarations. This is expected and fine for conjectures.
- Do not fetch existing solutions from the web.
