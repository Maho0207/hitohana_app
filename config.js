/* 一花交通 バス案内 — 設定
 * adminPasswordHash: 事業者用ページの8桁パスワードのハッシュ値（SHA-256）。
 *   初期パスワードは 20261027 です。公開前に必ず変更してください。
 *   事業者用ページ → 設定 → 「パスワードの変更」で表示される値をここに貼り付けます。
 * storagePrefix: ブラウザ保存（localStorage）のキーの先頭につける文字列。
 */
window.APP_CONFIG = {
  companyName: '一花交通',
  adminPasswordHash: '52e4af2715fa416fa570ed7ab1e4be53db3d7360811cd0f34c3ee76c11d51db3',
  storagePrefix: 'ichika.',
};
