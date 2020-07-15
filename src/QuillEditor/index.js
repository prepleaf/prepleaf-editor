import React, { useEffect, useRef } from 'react';
import Quill from 'quill';
import Delta from 'quill-delta';

const wordUnwatedCharRemover = (node, delta) => {
	try {
		if (node.getAttribute('style').indexOf('mso-spacerun:yes') > -1) {
			console.log('yaaayyyyyy, found.', node, delta);
			return new Delta();
		} else {
			// console.log(node.style, node.getAttribute('style'), node.style.msoSpectrum);
		}
	} catch (error) {
		// console.error(error);
	}
	return delta;
};

const QuillEditor = ({ htmlContent, readOnly }) => {
	const editorElemRef = useRef();
	const editor = useRef();
	useEffect(() => {
		editor.current = new Quill(editorElemRef.current, {
			modules: {
				clipboard: {
					matchers: [['span', wordUnwatedCharRemover]],
				},
			},
			readOnly,
		});
	}, []);
	useEffect(() => {
		const quill = editor.current;
		const delta = quill.clipboard.convert(htmlContent);
		quill.setContents(delta, 'api');
	}, [htmlContent]);

	useEffect(() => {
		editor.current.enable(!readOnly);
	}, [readOnly]);

	return (
		<div>
			<div ref={editorElemRef} />
		</div>
	);
};

QuillEditor.defaultProps = {
	htmlContent: '',
	readOnly: false,
};

export default QuillEditor;
