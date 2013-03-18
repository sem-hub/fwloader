fwloader
========

A loader for ipfw rules (FreeBSD) with some additional features like:
* Split too long rules (to pass FreeBSD opcodes limit)
* Labels for skip-to and rules blocks
* Progress bars for loading and installing rules

NOTE:
Not all keywoards implemented. Only a classical rules form is supported (no
mixed src/dst style).
