// Shared progressive enhancement for HTTP and the portable file:// export.
// prepare-v2-assets.py prepends the unchanged timeline and caption cues.
(function () {
  'use strict';
  const video = document.getElementById('pc2-overview-video');
  if (!video || typeof pc2FilmData === 'undefined' || video.dataset.initialized) return;
  const wrapper = video.closest('[data-media-base]');
  const description = document.getElementById('film-description');
  const title = description?.querySelector('h3');
  const detail = description?.querySelector('p');
  if (!wrapper || !description || !title || !detail) return;
  video.dataset.initialized = 'true';
  const { timeline, cues } = pc2FilmData;
  const buttons = Array.from(wrapper.querySelectorAll('.film-stages button'));
  const media = name => new URL(name, new URL(wrapper.dataset.mediaBase, document.baseURI)).href;
  let time = 0, pendingSeek = null, fallback = null, inlineTrack = null;
  // Media timestamps may round down to microseconds after seeking. This tolerance
  // keeps the selected chapter at its boundary without changing the seek target.
  const seekToleranceSeconds = 1e-6;
  const indexAt = (items, currentTime) => items.reduce((found, item, index) => currentTime + seekToleranceSeconds >= item.start ? index : found, 0);
  function update(currentTime) {
    time = currentTime;
    const state = timeline.states[indexAt(timeline.states, time)];
    title.textContent = state.title; detail.textContent = state.detail;
    const chapter = indexAt(timeline.chapters, time);
    buttons.forEach((button, index) => button.setAttribute('aria-pressed', String(index === chapter)));
    if (fallback) { fallback.src = media(state.id + '.jpg'); fallback.alt = state.title + '. ' + state.detail; }
  }
  function showFallback() {
    if (fallback) return;
    fallback = document.createElement('img'); fallback.className = 'film-fallback'; fallback.width = 1536; fallback.height = 1152;
    video.replaceWith(fallback);
    buttons.forEach(button => button.removeAttribute('aria-controls'));
    const message = document.createElement('p'); message.className = 'film-error';
    const link = (label, file) => { const a = document.createElement('a'); a.href = media(file); a.textContent = label; return a; };
    message.append('The video could not load. ', link('Open the video file', 'pc2-overview.mp4'), ', ', link('listen to the narration', 'pc2-overview.mp3'), ', or ', link('read the transcript', 'pc2-overview.txt'), '.');
    detail.after(message); update(time);
  }
  buttons.forEach((button, index) => button.addEventListener('click', () => {
    const start = timeline.chapters[index]?.start;
    if (start === undefined) return;
    update(start);
    if (fallback) return;
    if (video.readyState < 1) pendingSeek = start;
    else { pendingSeek = null; video.currentTime = start; }
  }));
  video.addEventListener('loadedmetadata', () => { if (pendingSeek !== null) { video.currentTime = pendingSeek; pendingSeek = null; } });
  for (const event of ['timeupdate', 'seeked']) video.addEventListener(event, () => { if (!fallback && pendingSeek === null) update(video.currentTime); });
  video.addEventListener('ended', () => update(timeline.duration));
  video.addEventListener('error', showFallback);
  video.querySelector('source')?.addEventListener('error', showFallback);
  const native = video.querySelector('track');
  function installInlineCaptions() {
    if (inlineTrack || typeof window.VTTCue !== 'function') return;
    if (native) { native.track.mode = 'disabled'; native.remove(); }
    inlineTrack = video.addTextTrack('captions', 'English', 'en'); inlineTrack.mode = 'hidden';
    cues.forEach(cue => inlineTrack.addCue(new VTTCue(cue.start, cue.end, cue.text)));
  }
  if (location.protocol === 'file:' || !native) installInlineCaptions();
  else { native.addEventListener('error', installInlineCaptions, { once: true }); native.track.mode = 'hidden'; if (native.readyState === 3) installInlineCaptions(); }
  if (video.error) showFallback();
  update(0);
})();
