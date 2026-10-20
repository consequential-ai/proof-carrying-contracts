# PC2 v2 illustration components

Historical generation record. For new illustrations, follow the [canonical PC2 illustration style](../illustration-style.md); the earlier prompt below is retained for provenance.

Mode: built-in image_gen. One generation request; no variants. Nine equal cell crops and WebP conversions are downstream mechanical processing only.

Requested source resolution: 3072 × 3072 pixels, minimum 1536 × 1536. Final dimensions will be recorded below.

## References

- /Users/cciliber/Dev/PC2/PC2-website/identity-prototypes/public/media/contract-film/execution-master.png
- /Users/cciliber/Dev/PC2/PC2-website/identity-prototypes/public/media/overview/signed.jpg

## Exact generation prompt

```text
Use case: illustration-story.
Asset type: reusable, text-free raster component sheet for a research website. Generate exactly ONE square image, requested output resolution 3072 × 3072 pixels (at least 1536 × 1536), containing nine isolated illustrated objects arranged on an invisible equal 3-by-3 grid. This is a sprite sheet of separate objects, NOT a finished diagram, narrative scene, slide, or interface.

Reference images: Image 1, execution-master.png, is the style reference for paper-and-ink architectural forms, cube devices, bluegrey cutaway walls and restrained drawing depth. Image 2, signed.jpg, is the style reference for the terracotta and slate cube identities and cream standing paper documents. Use ONLY their object appearance. Do not copy any scene composition, text, title, labels, arrows, connectors, signatures, or page framing from either reference.

Overall style: refined, light editorial isometric illustration; crisp charcoal ink contours, subtle pencil-like hatching limited to the objects, warm cream paper surfaces, restrained soft contact shadows, matte geometric forms. Flat opaque background of exactly #faf9f6 across the entire sheet, with NO background grain, mottling, vignette, gradient, shadows crossing cells, or heavy texture. Restrained palette: slate blue, warm terracotta, muted neutral teal, cream, charcoal. Match the supplied PC2 drawings while keeping the overall result light, clean, and academically credible, never glossy or science-fiction.

Precise layout: the square canvas is divided conceptually into NINE EQUAL square cells, three columns by three rows. NO visible grid, cell boundaries, borders, frames, dividers, or captions. Each object is centered within its own cell and wholly contained there. Each object's complete ink, hatching and contact shadow fits inside the central 70% of its cell in both dimensions, leaving at least 15% clear cell margin on all four sides. The nine object centers align consistently across rows and columns. Keep all nine objects separate, with generous empty paper between them. No object overlaps or connects to any other object.

Top row, left to right:
1. One slate-blue client cube device, cream front face plate, one dark circular recessed aperture. No eyes, face, arms or legs.
2. One warm terracotta contractor cube device, cream front face plate, one dark circular recessed aperture. Same size, orientation, construction and depth as the client cube.
3. One muted neutral-teal specialist cube device, cream front face plate, one dark circular recessed aperture. Same size, orientation, construction and depth as the other two cubes.
The three agents must have comparable visual size and matching silhouettes; color is their only identity difference.

Middle row, left to right:
4. One large standing cream paper contract document in shallow isometric perspective. Exactly three short abstract charcoal horizontal line marks, with no actual writing, signatures, symbols, seals or badge. It occupies about 65% of the cell's height.
5. One smaller standing cream subcontract document in the same perspective and style. Exactly three abstract charcoal horizontal line marks and no actual writing. Visibly smaller than the large contract: about 48% of its own cell's height.
6. One paired object composed of two slightly overlapping standing rectangular tiles: a cream action tile in front/left and a slate-blue proof tile behind/right. Plain abstract line marks only; no letters, equations, arrows, tick/check symbols, badges or seals. The combined pair fits within the central 70% of the cell.

Bottom row, left to right:
7. One single cream envelope/tool object in shallow isometric perspective, with a simple folded envelope flap. No other tool, no labels, no stamps, no writing.
8. One small bluegrey EMPTY cutaway Airlock enclosure, with visible ivory floor, restrained low front wall and taller back/side walls, one terracotta doorway opening in its right wall. No agent, document, furniture, padlock or icon inside it. Match the architectural style of reference image 1. The ENTIRE enclosure and its short contact shadow fit within the central 70% of the cell.
9. One short cream executed-record document stack, three or four slightly offset cream sheets in shallow isometric perspective. On the top sheet use three abstract short charcoal line marks only. No words, check symbols, badges, signatures, stamps or icons.

Absolutely no readable text, typography, letters, numbers, names, equation symbols, captions, logo, watermark, signatures, arrows, connector lines, wires, status indicators, badges, green safety seals, security padlocks, coins, currency, humanoid robots, human faces or people anywhere in the image. The conceptual numbering and object names in these instructions MUST NOT appear in the image. Deliver only the nine clean isolated object illustrations on a uniform flat off-white background.
```


## Outcome and inspection

One built-in generation request succeeded. No retries or style variants were generated. Original source returned by the tool: `/Users/cciliber/.codex/generated_images/01a0a1cc-325e-7153-b756-cecb227b0ceb/exec-69b79e05-5643-4e9b-8346-bb3918fb7c48.png`. The source remains there; `components-original.png` is an unchanged copy.

Actual source dimensions: **1254 × 1254 pixels**, below the requested 1536 × 1536 minimum despite the explicit 3072 × 3072 prompt. Exact division gives nine **418 × 418 pixel** cells. No upscaling was performed.

All nine objects and their order are correct. No text, labels, arrows, connection topology, humanoids, locks, badges, or generated logos appear. The three cube identities match in construction and approximate size. The Airlock is empty. All objects remain wholly inside their cells, and all nine WebP derivatives were visually inspected without clipping.

Limitations: the background is lightly varied off-white rather than perfectly uniform #faf9f6. The original's four corner RGB samples are (249,248,244), (251,249,245), (249,247,243), and (248,247,242). The requested central-70%-of-cell footprint was not achieved consistently: notably the large contract and Airlock are larger. Object alignment also varies within cells; the Airlock and record sit higher than the cube agents. These are isolated reusable components, not finished diagram layouts.

Processing: exact rectangular 3×3 crops, PNG optimization, and opaque WebP encoding at quality 88 with method 6. No masking, recoloring, resampling, invented shapes, background replacement, or drawing modifications. Each PNG was verified pixel-identical to its corresponding source rectangle; all PNG and WebP dimensions were verified as 418 × 418. Cell coordinates and full paths are in `manifest.json`.

Original PNG: 1,618,330 bytes. Original WebP derivative: 117,424 bytes.

| Component | PNG bytes | WebP bytes |
|---|---:|---:|
| client | 170,359 | 12,876 |
| contractor | 168,493 | 13,272 |
| specialist | 170,965 | 12,894 |
| contract | 171,968 | 11,350 |
| subcontract | 131,852 | 6,862 |
| action-proof | 195,412 | 16,082 |
| tool | 151,920 | 10,076 |
| airlock | 198,215 | 18,234 |
| record | 172,434 | 15,306 |
