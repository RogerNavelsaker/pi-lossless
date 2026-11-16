import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { ingestEntries } from "../packages/core/src/ingest.ts";
import { LcmStore } from "../packages/core/src/store.ts";

const store = new LcmStore(":memory:");
try {
  const result = ingestEntries(store, [
    { entryId: "bun-smoke", role: "user", text: "Bun SQLite smoke test", timestamp: 1 },
  ]);
  if (result.inserted !== 1 || !store.hasEntry("bun-smoke") || store.hasEntry("missing")) {
    throw new Error(`unexpected ingestion result: ${JSON.stringify(result)}`);
  }
  if (store.coveringSummaryId("missing") !== undefined || store.stats().messages !== 1) {
    throw new Error("Bun SQLite returned unexpected results for a missing row or message count");
  }
} finally {
  store.close();
}

const directory = mkdtempSync(join(tmpdir(), "lcm-bun-sqlite-smoke-"));
try {
  const path = join(directory, "store.db");
  const writable = new LcmStore(path);
  writable.close();

  const readOnly = new LcmStore(path, { readOnly: true });
  try {
    if (readOnly.stats().messages !== 0) {
      throw new Error("read-only Bun SQLite store returned an unexpected message count");
    }
  } finally {
    readOnly.close();
  }
} finally {
  rmSync(directory, { recursive: true, force: true });
}

console.log("Bun SQLite smoke test passed");
