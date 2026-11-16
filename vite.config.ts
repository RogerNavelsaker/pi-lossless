import { fileURLToPath } from "node:url";

import { defineConfig } from "vite-plus";

const coreSourceForTests = fileURLToPath(new URL("./packages/core/src/index.ts", import.meta.url));

export default defineConfig({
  fmt: {
    sortImports: true,
    sortPackageJson: true,
    ignorePatterns: ["apps/docs/content/**", "packages/pi/dist/**"],
  },
  lint: {
    options: {
      typeAware: true,
      typeCheck: true,
    },
    ignorePatterns: ["apps/docs/content/**", "packages/pi/dist/**"],
  },
  staged: {
    "*.{js,ts,md,json,yml,yaml}": "vp check --fix",
  },
  resolve: {
    alias: {
      "lossless-core": coreSourceForTests,
      "bun:sqlite": fileURLToPath(
        new URL("./packages/core/test/support/bun-sqlite-node.ts", import.meta.url),
      ),
    },
  },
  test: {
    setupFiles: ["./packages/core/test/setup.ts"],
    include: ["packages/*/test/**/*.test.ts"],
  },
});
