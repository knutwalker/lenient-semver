// To render as railroad, paste the content of this file at
// https://tabatkins.github.io/railroad-diagrams/generator.html
Diagram(
  Optional(NonTerminal('white space'), 'skip'),

  NonTerminal('major'),

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

  Choice(1,

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

    Skip(),

    Sequence(
      Choice(0,
        Terminal('-'),
        Terminal('.')
      ),
      OneOrMore(
        NonTerminal('pre-release'),
        Choice(0,
          Terminal('-'),
          Terminal('.')
        )
      ),
      Optional(
        Sequence(
          Terminal('+'),
          OneOrMore(
            NonTerminal('build'),
            Choice(0,
              Terminal('-'),
              Terminal('.')
            )
          )
        ),
        'skip'
      )
    )
  ),

  Optional(NonTerminal('white space'), 'skip'),
)
