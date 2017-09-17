# Comments
Ousia allows two types of comments:

    // Inline comments, and

    /* Multiline comments. */

Multiline comments can be nested, but are required to be properly nested.
Therefore, a comment like `/* /* */` will be rejected as having an unterminated
comment.

Inline comments should be used to explain design choices and code passages which
are difficult to read. Multiline comments should instead be used to temporarly
comment-out unused code or code documentation.
