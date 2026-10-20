/* oxlint-disable next/no-img-element -- Native images preserve artwork proportions; picture selects overview diagram layouts. */
import { c } from '@/lib/site-data';
const figures = {
  formation: { file: 'contract-formation', section: '4.3', altSection: '6.5', width: 960, height: 560 },
  execution: { file: 'proof-gated-execution', section: '4.4', altSection: '6.6', width: 960, height: 580 },
  delegation: { file: 'delegation', section: '4.5', altSection: '6.7', width: 960, height: 620 },
} as const;
export function SiteFigure({ kind }: { kind: keyof typeof figures }) {
  const f = figures[kind];
  return <figure className={`site-figure reading-column site-figure-${kind}`} aria-labelledby={`${kind}-caption`}>
    <picture>
      <source media="(max-width: 800px)" srcSet={`/media/site/${f.file}-mobile.svg`} />
      <img src={`/media/site/${f.file}-desktop.svg`} width={f.width} height={f.height} loading="lazy" alt={c(f.altSection, 1)} />
    </picture>
    <figcaption id={`${kind}-caption`}><strong>{c(f.section, 2)}</strong><p>{c(f.section, 3)}</p></figcaption>
  </figure>;
}
const homeIllustrations = [
  { file: 'home-contract-illustration.svg', raster: null, section: '6.2', width: 1180, height: 455 },
  { file: 'home-airlock-440.webp', raster: 'airlock', section: '6.3', width: 1536, height: 1024 },
  { file: 'home-delegation-440.webp', raster: 'delegation', section: '6.4', width: 1448, height: 1086 },
] as const;

function AirlockLabels() {
  return <div className="airlock-labels" aria-hidden="true">
    <svg viewBox="0 0 1536 1024" focusable="false">
      <g className="airlock-leaders">
        <path d="M500 130L594 257 M887 247L863 361 M660.48 887.36L867 540 M1383 480L1383 602" />
      </g>
    </svg>
    <span className="airlock-label airlock-label-contract">Contract</span>
    <span className="airlock-label airlock-label-check">Proof check</span>
    <span className="airlock-label airlock-label-proof">Request + proof</span>
    <span className="airlock-label airlock-label-email">e-mail<br />service</span>
  </div>;
}

export function HomeIllustration({ step }: { step: number }) {
  const illustration = homeIllustrations[step];
  return <div className="step-illustration"><div className="illustration-scene" style={{ aspectRatio: `${illustration.width} / ${illustration.height}` }}>
    <picture>
      {illustration.raster && <>
        <source media="(min-resolution: 2.5dppx)" srcSet={`/media/site/home-${illustration.raster}-1320.webp`} />
        <source media="(min-resolution: 1.5dppx)" srcSet={`/media/site/home-${illustration.raster}-880.webp`} />
      </>}
      <img src={`/media/site/${illustration.file}`} width={illustration.width} height={illustration.height} alt={c(illustration.section,1)} loading="lazy" decoding="async" />
    </picture>
    {illustration.raster === 'airlock' && <AirlockLabels />}
  </div></div>;
}
