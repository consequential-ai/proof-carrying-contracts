import type { Metadata } from 'next';
import { AirlockMark, type AirlockVariant } from '@/components/airlock-mark';
import { SiteHeader, SiteFooter } from '@/components/site-chrome';

export const metadata: Metadata = { title: 'Logo study', robots: { index: false, follow: false } };

const options: {
  variant: AirlockVariant;
  name: string;
  note: string;
  label: string;
}[] = [
  {
    variant: 'proof-chamber',
    name: 'Proof chamber',
    label: 'Earlier option',
    note: 'The existing inference-rule motif. Distinctive and balanced, with a less immediate connection to a familiar logical symbol.',
  },
  {
    variant: 'turnstile-chamber',
    name: 'Airlock + turnstile',
    label: 'Earlier option',
    note: 'The same airlock silhouette with a single turnstile inside. It connects proof checking to a recognisable boundary and stays clear at small sizes.',
  },
  {
    variant: 'bracket-turnstile',
    name: 'Bracketed turnstile',
    label: 'Selected mark',
    note: 'A proof symbol enclosed by a boundary. The mark also works as text, [ ⊢ ], giving PC2 a consistent identity in diagrams, documents, and conversation.',
  },
];

export default function IdentityPage() {
  return (
    <>
      <SiteHeader />
      <main id="main">
        <section
          className="subpage-hero shell"
          id="top"
          aria-labelledby="identity-title"
        >
          <p className="eyebrow">Identity study</p>
          <h1 id="identity-title">
            Three ways to
            <br />
            frame a proof.
          </h1>
          <p className="subpage-intro">
            The same colour, proportions, and line weight, compared at display
            and header sizes. The bracketed turnstile is the selected mark;
            the other two options are retained here as part of the design study.
          </p>
        </section>
        <section
          className="section shell logo-options"
          aria-label="Logo alternatives"
        >
          {options.map((option) => (
            <article
              className={`logo-option ${option.variant === 'bracket-turnstile' ? 'recommended-option' : ''}`}
              key={option.variant}
            >
              <p className="eyebrow">{option.label}</p>
              <div className="logo-specimen">
                <AirlockMark variant={option.variant} />
              </div>
              <h2>{option.name}</h2>
              <p>{option.note}</p>
              <div className="logo-wordmark">
                <AirlockMark variant={option.variant} />
                <span>
                  PC<sup>2</sup>
                </span>
                <span>
                  Proof Carrying
                  <br />
                  Contracts Protocol
                </span>
              </div>
              <a
                className="text-link"
                href={`/logos/pc2-${option.variant}.svg`}
                download
              >
                Download SVG
              </a>
            </article>
          ))}
        </section>
        <section className="section shell" aria-labelledby="turnstile-title">
          <div className="reading-column">
            <p className="eyebrow">The notation</p>
            <h2 id="turnstile-title">Why the single turnstile?</h2>
            <p>
              In its usual logical reading, ⊢ denotes derivability in a formal
              system: a conclusion follows by its rules. The double turnstile,
              ⊨, denotes semantic consequence: every model satisfying the
              premises also satisfies the conclusion.
            </p>
            <p>
              Both connect to PC2’s foundations. For the mark, ⊢ places the
              emphasis on the proof that accompanies an action and can be
              checked. The brackets suggest the boundary within which that
              proof governs an action, and can be written directly as [ ⊢ ].
            </p>
            <a
              className="text-link section-link"
              href="https://www.logicmatters.net/wp-content/uploads/2019/05/IFL2_Propositional_ND.pdf"
              target="_blank"
              rel="noreferrer"
            >
              Notation reference | Peter Smith, §24.5
            </a>
          </div>
        </section>
      </main>
      <SiteFooter />
    </>
  );
}
