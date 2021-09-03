# Prepleaf Editor

Dev server

```
npm run dev
```

Create build for distribution

```
npm run build
```

## Fonts

Copy all the fonts to your public root. Run the following command

```
cp -R node_modules/prepleaf-editor/lib/fonts public
```

Replace public with your root directory, like static, build

## Image proxy and url transformation

Pass transformImageUrl function as the prop
function signature

```
transformImageUrl(originalUrl:string): string
```

This can be used to load images from proxy
Example:

```
const transformImageUrl = (url) => {
	return `${url}${url.includes('?') ? '' : '?'}&size=120`;
};
```

Proxy images

```
const transformImageUrl = (url) => {
	return `https://images.prepleaf.com/?url=${encodeURIComponent(url)}`;
};

```
