# Note
While designing the language, this idea should always be applied: **Always tell
first the most important thing.** This means that modifiers should always come
after their arguments. For example, when designing an API for units, you should
be able to say

    metre.milli
    ton.long
    ton.short

This fees better than, say, `long_ton` or `millimetre`. Although these are more
similar to the natural language, they pose emphasis on what's unimportant.

Developers should be able to say when and how to use attributes or top-level
functions, and they should do so by distinct language constructs.
