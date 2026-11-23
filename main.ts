import { readdirSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Runs one tiny-stack program (bytes P) on input bytes B.
// Returns [outputBytes, exitCode]. Pure: no clock, no randomness, no I/O.
function run(P, B) {
  const n = P.length;
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory, all zero
  const out = [];
  let sp = 0, cp = 0, ip = 0, pc = 0, st = 0;
  for (;;) {
    if (st === 1000000) return [out, 10]; // step limit
    if (pc < 0 || pc >= n) return [out, 9]; // pc outside the program
    const o = P[pc];
    // Decode: immediate length, pops, pushes for this opcode.
    let im = 0, po = 0, pu = 0, known = 1;
    if (o === 1) { im = 1; pu = 1; }
    else if (o === 2) { im = 4; pu = 1; }
    else if (o === 3) po = 1;
    else if (o === 4) { po = 1; pu = 2; }
    else if (o === 5) { po = 2; pu = 2; }
    else if (o === 6) { po = 2; pu = 3; }
    else if (o === 7) { po = 3; pu = 3; }
    else if ((o >= 0x10 && o <= 0x16) || (o >= 0x18 && o <= 0x1a) || (o >= 0x1c && o <= 0x1e) || (o >= 0x20 && o <= 0x22)) { po = 2; pu = 1; }
    else if (o === 0x17 || o === 0x1b) { po = 1; pu = 1; }
    else if (o === 0x30 || o === 0x33) im = 2;
    else if (o === 0x31 || o === 0x32) { im = 2; po = 1; }
    else if (o === 0x40) { po = 1; pu = 1; }
    else if (o === 0x41 || o === 0x50 || o === 0x51 || o === 0x53) po = 1;
    else if (o === 0x52) pu = 1;
    else if (o !== 0 && o !== 0x34) known = 0;
    if (!known) return [out, 5]; // unknown opcode
    if (pc + im >= n) return [out, 9]; // immediate cut off by the end
    st++;
    const nx = pc + 1 + im;
    if (sp < po) return [out, 2]; // stack underflow
    if (sp - po + pu > 256) return [out, 3]; // stack overflow
    pc = nx;
    switch (o) {
      case 0x00: return [out, 0]; // HALT
      case 0x01: S[sp++] = (P[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: S[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: S[sp] = S[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
      case 0x06: S[sp] = S[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; } // ROT
      case 0x17: S[sp - 1] = -S[sp - 1] | 0; break; // NEG
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break; // NOT
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const r = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (o !== 0x30) { const v = S[--sp]; take = o === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + r;
        break;
      }
      case 0x33: // CALL
        if (cp === 64) return [out, 7];
        C[cp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return [out, 8];
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = S[sp - 1];
        if (a < 0 || a > 255) return [out, 6];
        S[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE ( v addr -- )
        const a = S[sp - 1], v = S[sp - 2];
        if (a < 0 || a > 255) return [out, 6];
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        const s = String(S[sp - 1]);
        if (out.length + s.length > 65536) return [out, 11];
        sp--;
        for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (out.length + 1 > 65536) return [out, 11];
        out.push(S[--sp] & 255);
        break;
      case 0x52: S[sp++] = ip < B.length ? B[ip++] : -1; break; // IN, -1 past the end
      case 0x53: return [out, S[--sp] & 255]; // EXIT with the low byte
      default: { // binary ops: ( a b -- r ), b is the top
        const b = S[sp - 1], a = S[sp - 2];
        let r;
        switch (o) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: if (b === 0) return [out, 4]; r = (a / b) | 0; break; // -2147483648 / -1 wraps to itself via |0
          case 0x14: if (b === 0) return [out, 4]; r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: if (b === 0) return [out, 4]; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return [out, 4]; r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        S[sp++] = r;
      }
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const P = readFileSync(join(I, id, 'program.bin'));
  const B = readFileSync(join(I, id, 'input.bin'));
  const [U, e] = run(P, B);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Buffer.from(U));
  writeFileSync(join(O, id, 'exit.txt'), e + '\n');
}
