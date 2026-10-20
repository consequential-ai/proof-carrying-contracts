import type { ComponentPropsWithoutRef } from 'react';

export function Paragraphs({ text, ...props }: { text: string } & ComponentPropsWithoutRef<'div'>) {
  return <div {...props}>{text.split('\n\n').map(p => <p key={p}>{p}</p>)}</div>;
}
