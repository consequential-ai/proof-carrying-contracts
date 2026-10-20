import type { ComponentPropsWithoutRef } from 'react';

// This is a static, multi-page site. Native links keep navigation independent
// of the framework's client router and also work without JavaScript.
export function SiteLink({
  children,
  ...props
}: ComponentPropsWithoutRef<'a'>) {
  return <a {...props}>{children}</a>;
}
