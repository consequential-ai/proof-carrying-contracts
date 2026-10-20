import type { Metadata } from 'next';
import { Geist, Source_Serif_4 } from 'next/font/google';
import './globals.css';
import './site-v2.css';
import { pageMetadata } from '@/lib/site-data';
const sans = Geist({ variable: '--font-sans', subsets: ['latin'] });
const serif = Source_Serif_4({
  variable: '--font-serif',
  weight: ['400', '600'],
  subsets: ['latin'],
});
export const metadata: Metadata = {
  ...pageMetadata('PC2 | Proof Carrying Contracts', 'An open protocol for enforceable agreements between AI agents representing different people and organisations.', '/'),
  icons: { icon: '/logos/pc2-bracket-turnstile.svg' },
};
export default function RootLayout({
  children,
}: Readonly<{ children: React.ReactNode }>) {
  return (
    <html lang="en">
      <body className={`${sans.variable} ${serif.variable}`}>{children}<script src="/site-v2.js" defer /></body>
    </html>
  );
}
