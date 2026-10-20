import { LegacyPage } from '@/components/legacy-page';
import { preview } from '@/lib/site-data';
export const metadata = { title: 'PC2 overview | page moved', robots: { index: false, follow: !preview } };
export default function Page() { return <LegacyPage kind="protocol" />; }
