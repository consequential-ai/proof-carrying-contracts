import Image from 'next/image';
import type { ReactNode } from 'react';

const illustrations = {
  formation: {
    src: '/media/protocol/contract-formation.png',
    alt: 'A contractor and a client develop a shared contract with the help of contract assistants. Both sign; payment is set aside and an Airlock is agreed before execution begins.',
    title: 'Contract formation',
    width: 1536,
    height: 1024,
  },
  runtime: {
    src: '/media/protocol/airlock-runtime.png',
    alt: 'Inside the Airlock, the contractor submits a call and proof to a checker. Rejected calls return to the agent without execution. Accepted calls reach designated tools for external resources, agreed evaluation, delegation or settlement. The signed contract and execution state govern checking.',
    title: 'Airlock execution',
    width: 1536,
    height: 1024,
  },
};

export function ProtocolIllustration({
  kind,
  children,
}: {
  kind: keyof typeof illustrations;
  children: ReactNode;
}) {
  const illustration = illustrations[kind];
  const captionId = `${kind}-illustration-caption`;

  return (
    <figure
      className={`protocol-illustration protocol-illustration-${kind}`}
      aria-labelledby={captionId}
    >
      <Image
        src={illustration.src}
        alt={illustration.alt}
        width={illustration.width}
        height={illustration.height}
        unoptimized
        loading="lazy"
      />
      <figcaption id={captionId}>
        <p>{children}</p>
        <a
          href={illustration.src}
          target="_blank"
          rel="noreferrer"
          aria-label={`View ${illustration.title.toLowerCase()} illustration at full size (opens in a new tab)`}
        >
          View full size <span aria-hidden="true">↗</span>
        </a>
      </figcaption>
    </figure>
  );
}
