import { SiteLink } from './site-link';
import timeline from '@/lib/overview-film.json';
import { c } from '@/lib/site-data';
export function ProcessFilm() {
  const state = timeline.states[0];
  return <figure className="process-film contract-film narrated-film" data-media-base="media/overview/" aria-label="A narrated introduction to Proof Carrying Contracts">
    <div className="film-topline"><span>From agreement to completion</span><span>1:50 · Narrated protocol illustration</span></div>
    <div className="film-screen contract-film-screen"><video id="pc2-overview-video" controls playsInline preload="metadata" poster="/media/overview/intro.jpg" aria-label="Proof Carrying Contracts: narrated overview" aria-describedby="film-description"><source src="/media/overview/pc2-overview.mp4" type="video/mp4" /><track kind="captions" src="/media/overview/pc2-overview.vtt" srcLang="en" label="English" /></video></div>
    <div className="film-controls"><nav className="film-stages" aria-label="Video chapters">{timeline.chapters.map((item,index)=><button key={item.label} type="button" aria-label={`Jump to ${item.label.toLowerCase()}`} aria-controls="pc2-overview-video" aria-pressed={index===0}><span className="stage-dot" aria-hidden="true" />{item.label}</button>)}</nav></div>
    <figcaption id="film-description" className="film-description"><h3>{state.title}</h3><p>{state.detail}</p><p className="film-concept-caption">{c('4.2',2)}</p><div className="film-document-links"><SiteLink href="/media/overview/pc2-overview.txt">Read the transcript</SiteLink><SiteLink href="/media/overview/pc2-overview.vtt" download>Download captions</SiteLink></div></figcaption>
    <script src="/film.js" defer />
  </figure>;
}
