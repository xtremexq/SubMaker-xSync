# Changelog

All notable changes to this project will be documented in this file.

## SubMaker xSync v1.0.9

**Improvements:**

- **Complete mode can now demux large regular MKVs from the local OPFS full download in chunked windows before falling back to targeted recovery:** after a full disk-backed download finishes, xSync can reuse the same OPFS temp file to build local subtitle windows, merge the recovered tracks, and only fall back again if that chunked pass cannot finish cleanly. This gives very large non-HLS MKVs a middle path between one-shot full demux and sparse range recovery.

- **Auto Subs full-stream jobs now keep large direct files on OPFS all the way into transcription prep:** the non-HLS Cloudflare / Assembly audio-extraction path now requests disk-backed full fetches with temp-file descriptors, keeps those descriptors through background window planning, and passes OPFS-backed inputs forward instead of remapping finished `2GB+` downloads into JS `ArrayBuffer`s before FFmpeg sees them.

- **Large OPFS-backed audio decode now uses the dedicated FFmpeg worker path instead of staged MEMFS copies:** when Auto Subs needs shared full-stream windows from an OPFS temp file, the offscreen page now mounts that temp file directly in the worker and decodes from there, avoiding the staged-copy branch that still had practical multi-GB limits. Demux/decode watchdog budgets now also scale with input size so long large-file runs do not time out prematurely.

- **Offscreen subtitle demux now classifies text-vs-bitmap FFmpeg failures more cleanly during worker and direct extraction:** batch/sequential text extraction can skip known non-text conversion mismatches, preserve bitmap/copy streams for detection instead of logging noisy failures, and avoid unnecessary flat-cue repair inside bounded chunked passes until the merged result is evaluated.

**Bug Fixes:**

- **Fixed Auto Subs still failing on `2GB+` direct files after Embedded Subtitles had already been hardened:** the autosubs audio path could still hit `Full fetch final memory map failed ...` or later multi-GB transfer failures because Embedded Complete extraction had been moved to disk-backed OPFS temp files while autosubs still re-materialized the same finished download in JS memory before offscreen decode. Large direct files now stay on the disk-backed path through Cloudflare / Assembly audio extraction, matching the embedded page's safer large-file behavior.

- **Fixed AssemblyAI full-video uploads rebuilding giant in-memory payloads from completed OPFS downloads:** the programmatic full-video request path now reads the finished OPFS temp file as a `File` / `Blob` for upload instead of reconstructing the entire payload as one large JS buffer first, keeping the large-file upload path consistent with the new disk-backed fetch flow.

- **Fixed Embedded Complete-mode full downloads still hanging forever after a stalled network read on large files:** some real `1.4-3 GB` runs could stop making progress mid-download even though partial data had already been written to OPFS. The full-fetch reader now times out idle reads, cancels the stuck stream, and resumes with HTTP Range requests from the last committed byte instead of waiting indefinitely.

- **Fixed transient OPFS disk-write failures aborting otherwise recoverable Complete-mode jobs:** when the browser lost the current writable handle during a large full download, xSync could fail the job or continue with a dead temp-file reference even though most of the file had already been written successfully. The OPFS writer now reopens with existing data preserved, re-measures the durable byte count, and resumes from that committed offset before later demux/recovery steps continue.

- **Fixed regular MKV subtitle planning missing streams whose headers sat deeper in the file or used larger EBML values:** the MKV header parser now performs a deeper second-pass scan when the shallow probe finds no tracks and uses safer large-value handling for EBML sizes/IDs, reducing false `no subtitle streams` cases on larger containers.

- **Fixed bitmap-only MKV subtitle jobs wasting time on OCR paths that are not implemented yet:** Complete-mode subtitle-plan preflight and the offscreen demuxer now detect image-based subtitle streams up front and stop immediately with `Image-based subtitle streams were detected, but OCR extraction is not implemented yet.` instead of attempting long OCR/Tesseract fallback work that cannot currently succeed.

- **Fixed long-running extract jobs being marked failed too early in the content script:** pending extract watchdogs now stay alive for up to 60 seconds, clear as soon as progress or debug-log traffic starts, tolerate more MV3 async-port-close variants, and treat unknown extraction modes conservatively as `complete` instead of silently collapsing back to `smart`.

## SubMaker xSync v1.0.8

**Improvements:**

- **Complete mode still downloads the full file, but no longer remaps the finished OPFS temp file back into background JS memory before demux:** Non-HLS Complete extraction now keeps the fully-downloaded stream on disk and hands an OPFS temp-file descriptor to the offscreen FFmpeg page instead of calling `file.arrayBuffer()` on the finished multi-GB temp file in the background worker. This removes the post-download `Full fetch final memory map failed ...` failure mode seen on larger files, while keeping Complete mode as a real full-file path. The offscreen demuxer can also mount the temp file via `WORKERFS` when available, reducing an additional large in-memory copy on very large streams.

- **Complete-mode full downloads now recover from transient network slips instead of restarting from byte 0:** The OPFS-backed full-fetch path now treats mid-stream read failures as resumable events, waits briefly, and retries up to 3 times using HTTP Range requests from the last successfully written byte. This means a failure around `200-300 MB` no longer forces Complete mode to throw away the whole partial download immediately before recovery even starts.

- **Embedded demux now preserves trusted subtitle language metadata more consistently across extraction modes:** MKV/MP4 header probing is used more aggressively, exact/regional tags are normalized more reliably (`pt-BR`, `pt-PT`, `es-419`, `zh-Hans`, `zh-Hant`, etc.), and content-based language guesses are treated as a weak fallback instead of a peer to real container metadata.

**Bug Fixes:**

- **Fixed Complete-mode range recovery surfacing truncated subtitle fragments as successful extraction results:** Recovery attempts now validate cue coverage, cue count, file size, and cue timeline quality before returning tracks. This prevents tiny early-fragment outputs from being treated as real recovered subtitles after a full-download demux failure.

- **Fixed Complete-mode truncated MKV demux attempts flooding extraction logs with FFmpeg stderr spam:** The offscreen log relay now suppresses repetitive FFmpeg banner/configuration output, repeated `Non-monotonous DTS` timestamp-repair lines, and other low-signal demux chatter from obviously incomplete buffers. It also skips the known `WORKERFS` fallback warning path when the environment cannot support that mount method, reduces staged-copy progress noise, and removes duplicate `Extraction failed:` phrasing from the terminal status update so the real failure message stays readable.

- **Fixed extracted subtitle tracks keeping stale guessed languages after trusted container/header metadata was discovered:** Header-based language application now replaces weak `content-guess` / `label` assignments instead of preserving their stale `languageRaw` / `languageSource` fields underneath the new language. This closes the class of bugs where FFmpeg/header metadata identified one language correctly but later steps could still surface a different guessed language.

- **Fixed label/content guessing and exact-tag normalization holes causing wrong-language carryover across the extraction pipeline:** xSync now normalizes exact BCP-47-ish forms before collapsing to the base subtag and avoids letting generated labels, placeholder names, or weak guesses outrank trusted metadata during later extraction/result-merging steps.

- **Fixed offscreen FFmpeg cleanup around early returns, cancellations, and fallback paths:** The offscreen demux/document flow now cleans up staged input files, extracted temp outputs, and mounted OPFS inputs more reliably so failed retries, OCR fallbacks, and cancelled jobs do not leave FFmpeg filesystem artifacts behind across runs.

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
