export type AirlockVariant =
  | 'proof-chamber'
  | 'turnstile-chamber'
  | 'bracket-turnstile';

export function AirlockMark({
  className = '',
  variant = 'bracket-turnstile',
}: {
  className?: string;
  variant?: AirlockVariant;
}) {
  return (
    <svg
      className={className}
      viewBox="0 0 64 64"
      fill="none"
      aria-hidden="true"
      stroke="currentColor"
      strokeWidth="3"
      strokeLinejoin="miter"
      strokeLinecap="square"
    >
      {variant === 'bracket-turnstile' ? (
        <path d="M17 12H8V52H17M47 12H56V52H47" />
      ) : (
        <path d="M8 24V12H56V24M8 40V52H56V40" />
      )}
      {variant === 'proof-chamber' ? (
        <path d="M23 24H29M35 24H41M21 32H43M29 40H35" strokeWidth="2.5" />
      ) : (
        <path d="M25 22V42M25 32H42" />
      )}
    </svg>
  );
}
