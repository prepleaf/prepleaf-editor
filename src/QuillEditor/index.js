import React, { useEffect, useRef } from 'react';
import Quill from 'quill';
import Delta from 'quill-delta';

const wordUnwatedCharRemover = (node, delta) => {
	try {
		const style = node.getAttribute('style');
		if (
			style.indexOf('mso-spacerun:yes') > -1 ||
			style.indexOf('mso-tab-count') > -1
		) {
			// console.log('yaaayyyyyy, found.', node, delta);
			return new Delta();
		} else {
		}
	} catch (error) {}
	return delta;
};

class QuillEditor extends React.Component {
	componentDidMount() {
		const { onChange } = this.props;
		this.quill = new Quill(this.editorElemRef, {
			modules: {
				clipboard: {
					matchers: [['span', wordUnwatedCharRemover]],
				},
			},
			readOnly: this.props.readOnly,
		});
		this.quill.on('text-change', () => {
			console.log('text-change');
			onChange && onChange(this.quill.getContents());
		});
		this.onContentsOrHtmlContentChange();
	}

	setHtmlContent = (htmlContent) => {
		const quill = this.quill;
		const delta = quill.clipboard.convert(htmlContent);
		quill.setContents(delta, 'api');
	};
	setContents = (contents) => {
		const quill = this.quill;
		quill.setContents(contents, 'api');
	};
	onContentsOrHtmlContentChange = () => {
		if (this.props.contents) {
			this.setContents(this.props.contents);
		} else if (this.props.htmlContent) {
			this.setHtmlContent(this.props.htmlContent);
		}
	};
	componentDidUpdate(prevProps) {
		const quill = this.quill;
		if (this.props.htmlContent !== prevProps.htmlContent) {
			this.onContentsOrHtmlContentChange();
		}
		// if (prevProps.htmlContent != this.props.htmlContent) {
		// 	this.setHtmlContent(this.props.htmlContent);
		// }
		if (prevProps.readOnly !== this.props.readOnly) {
			quill.enable(!this.props.readOnly);
		}
	}
	render() {
		return (
			<div>
				<div ref={this.handleEditorElemRef} />
			</div>
		);
	}
	handleEditorElemRef = (ref) => {
		this.editorElemRef = ref;
	};
}

QuillEditor.defaultProps = {
	htmlContent: '',
	readOnly: false,
};

const parseContent = (rawContent) => {
	try {
		// console.log(rawContent);
		return JSON.parse(rawContent);
	} catch (e) {
		console.log('unable to parse content, returning null');
		console.error(e);
		return null;
	}
};

class QuillEditorController extends React.Component {
	constructor(props, context) {
		super(props, context);
		this.state = {
			contents: parseContent(props.rawContent),
		};
	}
	componentDidMount() {
		const { customRef } = this.props;
		customRef && customRef(this);
	}
	componentWillUnmount() {
		const { customRef } = this.props;
		customRef && customRef(null);
	}

	get value() {
		return {
			rawContent: JSON.stringify(this.state.contents),
		};
	}
	render() {
		const { customRef, ...otherProps } = this.props;
		return (
			<QuillEditor
				{...otherProps}
				contents={this.state.contents}
				onChange={(contents) => {
					this.setState({ contents });
				}}
			/>
		);
	}
}

export default QuillEditorController;
