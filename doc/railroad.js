// To render as railroad, paste the content of this file at
// https://tabatkins.github.io/railroad-diagrams/generator.html
Diagram(
  Stack(
    Sequence(

      // leading whitespace is skipped
      Optional(NonTerminal('whitespace'), 'skip'),

      // leading v is allowed
      Choice(0,
        Skip(),
        Terminal('v'),
        Terminal('V')
      ),

      // whitespace after the v is skipped
      Optional(NonTerminal('whitespace'), 'skip'),

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

    // release and build identifiers
    Choice(1,

      // any identifiers are optional
      Skip(),

      // default pre-release and build parsing
      Sequence(
        // pre-release delimter
        Choice(0,
          Terminal('-'),
          Terminal('.')
        ),
        // followed by a pre-release identifier
        // or many of them delimited with the same delimiters
        OneOrMore(
          NonTerminal('pre-release'),
          Choice(0,
            Terminal('-'),
            Terminal('.')
          )
        ),

        // last optional but, the build identifiers
        Choice(0,
          Sequence(
            // build delimter
            Terminal('+'),
            // followed by a build identifier
            // or many of them delimited with the same delimiters as the pre-release identifiers
            OneOrMore(
              NonTerminal('build'),
              Choice(0,
                Terminal('-'),
                Terminal('.')
              )
            )
          ),
          Skip(),
        )
      ),

      // special branch into `.Final` or `.Release` build identifiers
      Sequence(
        Choice(1,
          Terminal('-'),
          Terminal('.'),
          Terminal('+'),
        ),
        Choice(0,
          Terminal('Final'),
          Terminal('Release')
        )
      ),
    ),

    // trailing whitespace is skipped
    Optional(NonTerminal('whitespace'), 'skip'),
  ),
)
