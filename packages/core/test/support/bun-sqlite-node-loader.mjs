import { registerHooks } from "node:module";

const adapter = new URL("./bun-sqlite-node.mjs", import.meta.url).href;

registerHooks({
  resolve(specifier, context, nextResolve) {
    if (specifier === "bun:sqlite") return { url: adapter, shortCircuit: true };
    return nextResolve(specifier, context);
  },
});
