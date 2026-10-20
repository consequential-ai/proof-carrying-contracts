// Exercise the actual film script against a minimal eventful media boundary.
// No browser is launched and no production configuration is changed.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
const timeline=JSON.parse(fs.readFileSync('lib/overview-film.json','utf8'));
const node=()=>({listeners:{},attrs:{},addEventListener(type,fn){this.listeners[type]=fn;},setAttribute(key,value){this.attrs[key]=value;}});
const buttons=timeline.chapters.map(node),title=node(),detail=node(),native={...node(),track:{},readyState:2};
const wrapper={dataset:{mediaBase:'media/overview/'},querySelectorAll(){return buttons;}};
const description={querySelector(selector){return selector==='h3'?title:detail;}};
let clock=0;
const video={...node(),dataset:{},readyState:4,closest(){return wrapper;},querySelector(selector){return selector==='track'?native:node();},
  get currentTime(){return clock;},set currentTime(t){clock=Math.floor(t*1e6)/1e6;this.listeners.seeked?.();}};
const document={getElementById(id){return id==='pc2-overview-video'?video:description;},baseURI:'http://localhost/data/overview.html'};
vm.runInNewContext(fs.readFileSync('scripts/static-film.js','utf8'),{pc2FilmData:{timeline,cues:[]},document,location:{protocol:'http:'},URL});
for (let i=0;i<buttons.length;i++) {
  buttons[i].listeners.click();
  assert.equal(buttons.findIndex(b=>b.attrs['aria-pressed']==='true'),i,`Rounded seek for ${timeline.chapters[i].label}`);
  const state=timeline.states.findLast(s=>s.start<=timeline.chapters[i].start);
  assert.equal(title.textContent,state.title);
  if(i>0){clock=timeline.chapters[i].start-.001;video.listeners.timeupdate();assert.equal(buttons.findIndex(b=>b.attrs['aria-pressed']==='true'),i-1,'Do not select a later chapter 1ms early');}
}
console.log('PASS: all ten rounded seeks select the intended chapter and caption; no transition 1ms early.');
