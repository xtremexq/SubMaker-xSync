# Changelog

All notable changes to this project will be documented in this file.

## SubMaker xSync v1.0.8

**Improvements:**

- **Complete mode still downloads the full file, but no longer remaps the finished OPFS temp file back into background JS memory before demux:** Non-HLS Complete extraction now keeps the fully-downloaded stream on disk and hands an OPFS temp-file descriptor to the offscreen FFmpeg page instead of calling `file.arrayBuffer()` on the finished multi-GB temp file in the background worker. This removes the post-download `Full fetch final memory map failed ...` failure mode seen on larger files, while keeping Complete mode as a real full-file path. The offscreen demuxer can also mount the temp file via `WORKERFS` when available, reducing an additional large in-memory copy on very large streams.

- **Complete-mode full downloads now recover from transient network slips instead of restarting from byte 0:** The OPFS-backed full-fetch path now treats mid-stream read failures as resumable events, waits briefly, and retries up to 3 times using HTTP Range requests from the last successfully written byte. This means a failure around `200-300 MB` no longer forces Complete mode to throw away the whole partial download immediately before recovery even starts.

- **Mounted OPFS demuxes now get a dedicated FFmpeg-worker path before falling back to the direct offscreen core:** xSync can boot a separate demux worker for mounted-file extraction, batch text subtitle conversion more aggressively, and keep bitmap/copy tracks available for OCR fallback without immediately forcing a staged copy back through the main offscreen page.

- **Sync and auto-sub now stop for explicit multi-audio track selection instead of silently committing to the first stream:** When a container exposes multiple audio tracks, xSync can surface the choices back to the page, resume once the user picks a stream, and carry the chosen track language through the Cloudflare / AssemblyAI setup path more consistently.

- **MV3 background startup now preloads ALASS / ffsubsync WebAssembly modules during bootstrap:** The service worker eagerly imports the required wasm wrappers/glue while it is first evaluated, avoiding late `importScripts()` / CSP edge cases that could leave advanced sync engines unavailable after a cold wake-up.

- **Embedded demux now preserves trusted subtitle language metadata more consistently across extraction modes:** MKV/MP4 header probing is used more aggressively, exact/regional tags are normalized more reliably (`pt-BR`, `pt-PT`, `es-419`, `zh-Hans`, `zh-Hant`, etc.), and content-based language guesses are treated as a weak fallback instead of a peer to real container metadata.

**Bug Fixes:**

- **Fixed Complete-mode range recovery surfacing truncated subtitle fragments as successful extraction results:** Recovery attempts now validate cue coverage, cue count, file size, and cue timeline quality before returning tracks. This prevents tiny early-fragment outputs from being treated as real recovered subtitles after a full-download demux failure.

- **Fixed Complete-mode truncated MKV demux attempts flooding extraction logs with FFmpeg stderr spam:** The offscreen log relay now suppresses repetitive FFmpeg banner/configuration output, repeated `Non-monotonous DTS` timestamp-repair lines, and other low-signal demux chatter from obviously incomplete buffers. It also skips the known `WORKERFS` fallback warning path when the environment cannot support that mount method, reduces staged-copy progress noise, and removes duplicate `Extraction failed:` phrasing from the terminal status update so the real failure message stays readable.

- **Fixed extracted subtitle tracks keeping stale guessed languages after trusted container/header metadata was discovered:** Header-based language application now replaces weak `content-guess` / `label` assignments instead of preserving their stale `languageRaw` / `languageSource` fields underneath the new language. This closes the class of bugs where FFmpeg/header metadata identified one language correctly but later steps could still surface a different guessed language.

- **Fixed label/content guessing and exact-tag normalization holes causing wrong-language carryover across the extraction pipeline:** xSync now normalizes exact BCP-47-ish forms before collapsing to the base subtag and avoids letting generated labels, placeholder names, or weak guesses outrank trusted metadata during later extraction/result-merging steps.

- **Fixed offscreen FFmpeg cleanup around early returns, cancellations, and fallback paths:** The offscreen demux/document flow now cleans up staged input files, extracted temp outputs, and mounted OPFS inputs more reliably so failed retries, OCR fallbacks, and cancelled jobs do not leave FFmpeg filesystem artifacts behind across runs.

- **Fixed extracted text subtitle tracks from some containers coming back with flat or non-monotonic cue timelines:** xSync now detects obviously broken timestamp shapes, retries text extraction with PTS normalization, and can remux/reconvert only the affected subtitle streams before returning the final tracks.

- **Fixed sync / auto-sub choosing the wrong audio stream or carrying the wrong language hint on multi-track media:** Track preference now pauses for user choice when needed, reuses the selected stream across retries, and normalizes provider-specific language tags more reliably before transcription requests are built.

## SubMaker xSync v1.0.7

**New Features:**

- **OPFS-based full-stream buffering for large downloads:** Full-stream fetches no longer have to rely only on a single large in-memory buffer. Added an OPFS-backed download path (`fetchFullStreamBufferOPFS()`) plus a `fetchFullStream()` dispatcher so Complete-mode extraction, full-stream audio retries, and AssemblyAI full-video uploads can stream to disk first, then read the finished file back as an `ArrayBuffer`. If OPFS is unavailable, xSync falls back to the legacy RAM path automatically.

- **Stream Buffer Mode setting:** Added a new `Stream Buffer Mode` dropdown under `General -> Global Behaviour` with `Disk (default)` and `RAM`. The setting is stored in `chrome.storage.sync` under `xsync-settings.streamBufferMode`, with Disk as the safe default for large streams.

- **Linked Host banner in the popup:** The popup now shows the currently linked SubMaker host directly under the status card, making it easier to see whether the extension is pointed at a local server or the hosted fallback without opening settings first.

**Improvements:**

- **Complete mode now avoids unsafe multi-GB in-browser downloads and tries range-based recovery first:** Added a 3 GiB in-browser safety ceiling for non-HLS full fetches. Before committing to a full download, xSync now performs a light probe; if the stream is too large, it skips the unsafe full fetch and tries targeted recovery instead. The recovery flow can reuse the head sample, probe MKV cues/clusters, stream progressive coverage slices, combine head+tail buffers, and try a mid-file probe before giving up.

- **Embedded extraction jobs now support end-to-end cancellation:** Extraction runs now create tracked job records with `AbortController` support, and cancellation propagates through redirect resolution, range/full fetches, offscreen demux/decode, and video-based extraction via `OFFSCREEN_CANCEL`. This prevents overlapping runs on the same tab and reduces stuck extractions after page resets or retried requests.

- **Protected-host compatibility is more consistent across extraction retries:** Page-derived headers are now carried through more extraction paths, including redirect resolution, DASH text-track fetches, sample/range/tail probes, full downloads, and Complete-mode recovery paths, improving behavior on hosts that require request context from the active page.

- **MKV subtitle extraction is more targeted and more transparent when buffers are incomplete:** Offscreen demux now probes subtitle track metadata from MKV headers, prefers text subtitle streams explicitly, remuxes per planned stream when needed, and logs when the container advertises subtitle tracks but the current buffer still does not contain enough subtitle packets to extract them cleanly.

- **Popup version display now reads the real manifest version at runtime:** The visible popup version badge now uses `chrome.runtime.getManifest().version` instead of relying only on the fallback constant.

**Bug Fixes:**

- **Fixed FFmpeg bare-core extraction silently doing nothing:** The bare-core path previously treated missing `exec` / `callMain` entry points as a successful run, which could make subtitle extraction appear to succeed while producing no tracks. The offscreen loader now defaults back to the wrapper-based FFmpeg path, and missing bare-core entry points now throw an explicit error instead of failing silently.

- **Fixed duplicate/racy extract response handling in the content script:** Embedded extraction requests now treat the initial background reply as an acknowledgement and wait for the tab result relay, instead of immediately forwarding a second result to the page.

- **Fixed offscreen video extraction cleanup around cancels and timeouts:** Video-based extraction now tracks per-job cancellation, cleans up timers and text-track state more reliably, and avoids hanging or double-settling when tracks load late, time out, or the extraction is cancelled mid-run.
