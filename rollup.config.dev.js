import resolve from "@rollup/plugin-node-resolve";
import babel from "rollup-plugin-babel";
import commonjs from "@rollup/plugin-commonjs";
import livereload from "rollup-plugin-livereload";
import { terser } from "rollup-plugin-terser";
import injectProcessEnv from "rollup-plugin-inject-process-env";

export default {
  input: "examples/index.js",
  output: {
    file: "examples/build/bundle.js",
    format: "cjs"
  },
  plugins: [
    resolve(),
    babel({
      exclude: "node_modules/**" // only transpile our source code
    }),
    commonjs(),
    injectProcessEnv({
      NODE_ENV: "development"
    }),
    serve(),

    // Watch the `public` directory and refresh the
    // browser on changes when not in production
    livereload("public")

    // If we're building for production (npm run build
    // instead of npm run dev), minify
  ],
  external: []
};

function serve() {
  let started = false;

  return {
    writeBundle() {
      if (!started) {
        started = true;

        require("child_process").spawn("npm", ["run", "start", "--", "--dev"], {
          stdio: ["ignore", "inherit", "inherit"],
          shell: true
        });
      }
    }
  };
}
