## Developer Guide

A quick guide to some project-specific properties of this repo.

### Rich Docs

The project is set-up so that you can generate rich docs with support for 
mermaid diagrams and KaTeX with `cargo make rich-doc`. To use KaTeX, wrap
your math in $ ... $ or $$ ... $$ for block expressions. For mermaid, just
use a code block with language set to mermaid.

### `shields_up` Feature

There is a special feature which you can use to enable additional pre/post
condition checks. It is on by default, so make sure to disable it when
running benchmarks or public releases. Internal releases should probably
have `shields_up` enabled since they are often used to test and expose problems.

Remember that performance impact of `shields_up` does not have to be very
big - depends on the task. But it can also be significant, so if the code is 
taking a really long time to run, you can also try a build where the feature 
is disabled (assuming you trust the code).

### Code Coverage and CI

The project is configured for Travis with tarpaulin code coverage measurement.
Tarpaulin is not cross platform so you probably can't use it locally unless 
you are running on linux (even then there are some caveats). The best way
to test coverage is usually to actually push the code. 