// To render as railroad, paste the content of this file at
// https://tabatkins.github.io/railroad-diagrams/generator.html
// For documentation on what this means, visit
// http://tabatkins.github.io/railroad-diagrams/
Diagram(
  Stack(
    Sequence(

      // leading whitespace is skipped
      Choice(1, NonTerminal('whitespace'), Skip()),

      // leading v is allowed
      Choice(2,
        Terminal('V'),
        Terminal('v'),
        Skip(),
      ),

      // require at least the major version
      NonTerminal('major'),

      // the following minor and patch versions are optional
      Optional(
        Sequence(
          Terminal('.'),
          NonTerminal('minor'),
          Optional(
            Sequence(
              Terminal('.'),
              NonTerminal('patch')
            )
          )
        )
      ),

    ),

    // regular numbers
    Optional(
      Sequence(
        OneOrMore(
          Terminal('.'),
          NonTerminal('number'),
        ),
        Comment("Parses as build identifier"),
      ),
      'skip'
    ),

    // release and build identifiers
    Choice(0,

      // optional pre-release and build parsing
      Sequence(

        // optional pre-release parsing
        Choice(1,
          // pre-release identifiers are optional
          Skip(),
          // pre-release parsing
          Sequence(
            // pre-release delimter
            Choice(0,
              Terminal('-'),
              Terminal('.'),
            ),
            // followed by a pre-release identifier
            // or many of them delimited with the same delimiters
            OneOrMore(
              NonTerminal('pre-release'),
              Choice(0,
                Terminal('.'),
                Terminal('-'),
              )
            ),
          ),
        ),

        // optional build parsing
        Choice(1,
          // build identifiers are optional
          Skip(),
          // build parsing
          Sequence(
            // build delimter
            Terminal('+'),
            // followed by a build identifier
            // or many of them delimited with the same delimiters as the pre-release identifiers
            OneOrMore(
              NonTerminal('build'),
              Choice(0,
                Terminal('.'),
                Terminal('-'),
              )
            ),
          ),
        )
      ),

      // special branch into `.Final` or `.Release` build identifiers
      Sequence(
        Choice(1,
          Terminal('-'),
          Terminal('.'),
          Terminal('+'),
        ),
        Choice(1,
          Terminal('Final'),
          Terminal('Release'),
          Terminal('r'),
        ),
        Comment("Parses as build identifier"),
      ),
    ),

    // trailing whitespace is skipped
    Choice(1, NonTerminal('whitespace'), Skip()),
  ),
)
